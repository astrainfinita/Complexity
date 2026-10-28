/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Complexity.Encoding.Option
public import Complexity.Models.TreeMachine.Language.Verification
public import Complexity.Models.TreeMachine.Language.CaseView
public meta import Lean.Elab.Deriving.Util
public meta import Lean.Meta.Inductive
public meta import Lean.Meta.Match.Basic

/-! # Deriving tree representations and source operations

`@[tree_encoding]` generates a unique tree encoding and source operations for a
first-order inductive type. Single-constructor types omit the tag; fixed-arity fields
omit a final list terminator. Constructor fields supplied by the result indices are erased;
fixed constructor indices are checked by the decoder.

`tree_encoding T` also accepts non-recursive type families exposed through definitions
or structure fields, preserving `T` in the generated API in the current namespace.
-/

public meta section

namespace Complexity.TreeProgram.Deriving

open Lean Parser.Term Meta Elab Deriving Command

private structure Target where
  ind : InductiveVal
  levels : List Level
  /-- Closed family with its complete parameter telescope. -/
  family : Lean.Expr
  /-- Each binder is either captured or corresponds to an inductive argument. -/
  arguments : Array (Option Nat)
  ns : Name

private structure Header extends Lean.Elab.Deriving.Header where
  parameters : Array Term
  captures : Array Term

private def explicitBinders : Lean.Expr → Lean.Expr
  | .forallE name ty body _ => .forallE name ty (explicitBinders body) .default
  | .lam name ty body _ => .lam name ty (explicitBinders body) .default
  | e => e

private def Target.app (target : Target) (parameters args : Array Term) : TermElabM Term := do
  let family ← withOptions (·.setBool `pp.explicit true) do
    PrettyPrinter.delab (explicitBinders target.family)
  let args := target.arguments.mapIdx fun i arg => arg.elim parameters[i]! (args[·]!)
  `($family $args:term*)

private def Header.ref (header : Header) (name : Name) : TermElabM Term :=
  if header.captures.isEmpty then pure (mkIdent name)
  else `($(mkIdent name) $header.captures:term*)

private def closedPattern (index : Lean.Expr) : MetaM Lean.Expr := do
  try
    withTransparency .default <| (← Match.toPattern index).toExpr
  catch _ =>
    throwError "Tree encoding requires closed constructor indices to reduce to patterns; \
      cannot match {index}"

private def indexFields (ind : InductiveVal) (ctor : ConstructorVal) :
    MetaM (Array (Option Nat)) :=
  forallTelescopeReducing ctor.type fun xs result => do
    let mut fields := #[]
    for index in result.getAppArgs[ind.numParams...*] do
      let field := (xs.extract ind.numParams xs.size).idxOf? index
      if (field.isNone && index.hasFVar) || (field.isSome && fields.contains field) then
        throwError "Tree encoding requires constructor result indices to be distinct fields \
          or closed patterns"
      if field.isNone then discard <| closedPattern index
      fields := fields.push field
    return fields

private def dataFields (ind : InductiveVal) (ctor : ConstructorVal) : MetaM (Array Nat) := do
  let indices ← indexFields ind ctor
  return (List.range ctor.numFields).toArray.filter fun i => !indices.contains (some i)

private def withInstances {α : Type} (types : List Lean.Expr) (k : TermElabM α) : TermElabM α :=
  match types with
  | [] => k
  | ty :: types => do
    withLocalDecl (← mkFreshUserName `inst) .instImplicit ty fun _ =>
      withInstances types k

private def encodingRequirements (target : Target) : TermElabM (Array Term) := do
  let ind := target.ind
  forallBoundedTelescope (ind.type.instantiateLevelParams ind.levelParams target.levels)
      ind.numParams fun params _ => do
    let mut requirements := #[]
    for param in params do
      try
        let ty ← mkAppM ``UniqueEncoding #[mkConst ``Tree, param]
        if ← isTypeCorrect ty then requirements := requirements.push ty
      catch _ => pure ()
    for name in ind.ctors do
      let ctor ← getConstInfoCtor name
      let data ← dataFields ind ctor
      let ty ← inferType (mkAppN (mkConst name target.levels) params)
      requirements ← forallTelescopeReducing ty fun xs _ => do
        let mut requirements := requirements
        for i in data do
          let fieldType ← inferType xs[i]!
          if fieldType.isAppOf ind.name then continue
          let goal ← mkAppM ``UniqueEncoding #[mkConst ``Tree, fieldType]
          let found ← withInstances requirements.toList <| synthInstance? goal
          unless found.isSome do
            let requirement := explicitBinders (← mkForallFVars (xs.extract 0 i) goal
              (usedOnly := true))
            unless params.any (requirement.containsFVar ·.fvarId!) do
              throwError "Tree encoding needs an instance of {goal}"
            requirements := requirements.push requirement
        return requirements
    requirements.mapM fun ty => do
      withOptions (·.setBool `pp.funBinderTypes true) do
        PrettyPrinter.delab (explicitBinders (← mkLambdaFVars params ty))

private def freshBinders : Lean.Expr → TermElabM Lean.Expr
  | .forallE name ty body bi => do
    return .forallE (← mkFreshUserName name.eraseMacroScopes) ty (← freshBinders body) bi
  | e => pure e

/-- Keep captured parameters explicit, including those erased by unfolding the family. -/
private def mkHeader (arity : Nat) (target : Target) : TermElabM Header := do
  let ind := target.ind
  forallTelescope (← freshBinders (← inferType target.family)) fun xs _ => do
    let names ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName
    let parameters := names.map fun n => (mkIdent n : Term)
    let captures := parameters.zip target.arguments |>.filterMap fun (p, i) =>
      if i.isNone then some p else none
    let argNames := (Array.range (ind.numParams + ind.numIndices)).map fun i =>
      names[(target.arguments.idxOf? (some i)).get!]!
    let targetType ← target.app parameters (argNames.map fun n => (mkIdent n : Term))
    let mut binders ← xs.mapIdxM fun i x => do
      let name := mkIdent names[i]!
      let ty ← PrettyPrinter.delab (← inferType x)
      if target.arguments[i]!.isSome then `(bracketedBinder| {$name : $ty})
      else `(bracketedBinder| ($name : $ty))
    let params := (argNames.extract 0 ind.numParams).map mkIdent
    let instances ← (← encodingRequirements target).mapM fun requirement =>
      `(bracketedBinder| [($requirement $params:term*)])
    binders := binders ++ instances
    let targetNames ← (List.range arity).toArray.mapM fun _ => mkFreshUserName `x
    for name in targetNames do
      binders := binders.push (← `(bracketedBinder| ($(mkIdent name) : $targetType)))
    return { binders, argNames, targetNames, targetType, parameters, captures }

/-- The same constructor shape drives encoding, source construction and field access. -/
private inductive Shape where
  | nil
  | field (i : Nat)
  | pair (a b : Shape)
  deriving BEq

private def tag : Nat → Shape
  | 0 => .nil
  | n + 1 => .pair .nil (tag n)

private def fields : List Nat → Shape
  | [] => .nil
  | [i] => .field i
  | i :: is => .pair (.field i) (fields is)

/-- The shape of a tuple of `n` fields. -/
private def fields' (n : Nat) : Shape := fields (List.range n)

private def ctorShape (ind : InductiveVal) (ctor : ConstructorVal) : MetaM Shape := do
  if ind.name == ``List then
    return if ctor.cidx = 0 then .nil else .pair (.field 0) (.field 1)
  else if ind.name == ``Option then
    return if ctor.cidx = 0 then .nil else .pair .nil (.field 0)
  else if ind.name == ``Bool then
    return if ctor.cidx = 0 then .nil else .pair .nil .nil
  else
    let payload := fields (List.range (← dataFields ind ctor).size)
    return if ind.ctors.length = 1 then payload else .pair (tag ctor.cidx) payload

private def Shape.term (s : Shape) (args : Array Term) (nil pair : Name) : TermElabM Term :=
  match s with
  | .nil => pure (mkCIdent nil)
  | .field i => pure args[i]!
  | .pair a b => do
    let a ← a.term args nil pair
    let b ← b.term args nil pair
    `($(mkCIdent pair) $a $b)

private def rootIdent (n : Name) : Ident := mkIdent (`_root_ ++ privateToUserName n)

private def checkExisting (target : Target) : TermElabM Unit := withoutExporting do
  let header ← mkHeader 0 target
  Term.elabBinders (header.binders.map (·.raw)) fun _ => do
    let ty ← Term.elabTerm header.targetType none
    if (← synthInstance? (← mkAppM ``Encoding #[mkConst ``Tree, ty])).isSome then
      throwError "This type family already has a tree encoding; \
        deriving would change its representation"

private def checkType (ind : InductiveVal) : TermElabM Unit := do
  if ind.name == ``Nat then
    throwError "Nat needs its binary encoding, not the default constructor encoding"
  if ind.isNested || ind.isReflexive || ind.all.length != 1 then
    throwError "Tree encoding currently supports non-nested, non-mutual first-order inductive types"
  if ind.isRec && ind.ctors.length = 1 then
    throwError "Tree encoding cannot erase the only constructor tag of a recursive type"
  forallTelescopeReducing ind.type fun _ sort => do
    if sort == mkSort .zero then
      throwError "Tree encoding supports data types, not propositions"
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let data ← dataFields ind ctor
    forallTelescopeReducing ctor.type fun xs _ => do
      for i in data do
        let ty ← whnf (← inferType xs[ctor.numParams + i]!)
        if (← isProp ty) || ty.isSort then
          throwError "Tree encoding does not support proof or type-valued field \
            {xs[ctor.numParams + i]!}"

private def mkEncode (target : Target) (enc : Name) : TermElabM Command := do
  let ind := target.ind
  let header ← mkHeader 1 target
  let discrs ← mkDiscrs header.toHeader ind
  let mut alts := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let data ← dataFields ind ctor
    let alt ← forallTelescopeReducing ctor.type fun xs _ => do
      let mut pats : Array Term := Array.replicate ctor.numParams (← `(_))
      let mut args := #[]
      for i in [:ctor.numFields] do
        let a := mkIdent (← mkFreshUserName `a)
        pats := pats.push a
        unless data.contains i do continue
        let ty ← inferType xs[ctor.numParams + i]!
        args := args.push (← if ty.isAppOf ind.name then `($(← header.ref enc) $a)
          else ``(encode Tree $a))
      let rhs ← (← ctorShape ind ctor).term args ``Tree.nil ``Tree.pair
      let indices : Array Term ← (List.range ind.numIndices).toArray.mapM fun _ => `(_)
      let pattern ← `(@$(mkCIdent c):ident $pats:term*)
      let patterns := indices.push pattern
      `(matchAltExpr| | $[$patterns:term],* => $rhs)
    alts := alts.push alt
  let body ← `(match $[$discrs],* with $alts:matchAlt*)
  `(/-- The generated structural encoder; use `encode Tree` and its constructor equations. -/
    @[expose] def $(rootIdent enc):ident $header.binders:bracketedBinder* : Tree := $body)

private def mkDecode (target : Target) (dec : Name) : TermElabM Command := do
  let ind := target.ind
  let header ← mkHeader 0 target
  let params := (header.argNames.extract 0 ind.numParams).map mkIdent
  let mut alts := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let indices ← indexFields ind ctor
    let alt ← forallTelescopeReducing ctor.type fun xs result => do
      let mut raw := #[]
      let mut values := #[]
      let mut decoded := #[]
      let mut decoders := #[]
      for i in [:ctor.numFields] do
        if let some j := indices.idxOf? (some i) then
          values := values.push (mkIdent header.argNames[ind.numParams + j]!)
          continue
        let r := mkIdent (← mkFreshUserName `r)
        let a := mkIdent (← mkFreshUserName `a)
        raw := raw.push r
        values := values.push a
        decoded := decoded.push a
        let ty ← inferType xs[ctor.numParams + i]!
        decoders := decoders.push (← if ty.isAppOf ind.name then `($(← header.ref dec) $r)
          else ``(decode _ $r))
      let pattern ← (← ctorShape ind ctor).term raw ``Tree.nil ``Tree.pair
      let mut rhs ← ``(Part.some (@$(mkCIdent c) $params:term* $values:term*))
      for i in (List.range decoded.size).reverse do
        let a := decoded[i]!
        rhs ← ``(Part.bind $(decoders[i]!) (fun $a:ident => $rhs))
      let mut discrs := #[]
      let mut patterns := #[]
      let resultIndices := result.getAppArgs.extract ind.numParams result.getAppNumArgs
      for j in [:indices.size] do
        if indices[j]!.isSome then continue
        discrs := discrs.push (← mkDiscr header.argNames[ind.numParams + j]!)
        patterns := patterns.push (← PrettyPrinter.delab (← closedPattern resultIndices[j]!))
      unless discrs.isEmpty do
        let fallback ← patterns.mapM fun _ => `(_)
        -- A singleton index type can make the rejection branch unreachable.
        rhs ← `(set_option match.ignoreUnusedAlts true in match $[$discrs],* with
          | $[$patterns:term],* => $rhs
          | $[$fallback:term],* => Part.none)
      `(matchAltExpr| | $pattern => $rhs)
    alts := alts.push alt
  let exhaustive ← match ind.ctors with
    | [c] => do pure ((← dataFields ind (← getConstInfoCtor c)).size == 1)
    | _ => pure false
  unless exhaustive do
    alts := alts.push (← `(matchAltExpr| | _ => Part.none))
  let body ← `(fun $alts:matchAlt*)
  `(/-- The generated partial parser, rejecting trees outside the chosen representation. -/
    @[expose] def $(rootIdent dec):ident $header.binders:bracketedBinder* :
      Tree → Part $header.targetType := $body)

private def mkCorrect (target : Target) (enc dec correct : Name) : TermElabM Command := do
  let header ← mkHeader 1 target
  let a := mkIdent header.targetNames[0]!
  -- Follow each input separately instead of crossing constructors with decoder branches.
  `(theorem $(rootIdent correct):ident $header.binders:bracketedBinder* (t : Tree) :
      $a ∈ $(← header.ref dec) t ↔ $(← header.ref enc) $a = t := by
    constructor
    · revert $a:ident
      -- Keep recursive calls intact, avoiding extra matcher congruence proofs.
      set_option tactic.fun_induction.unfolding false in
        first | fun_induction $(mkIdent dec) | fun_cases $(mkIdent dec)
      all_goals intro $a:ident h
      all_goals simp only [$(mkIdent dec):term, Part.mem_bind_iff, Part.mem_some_iff,
        Part.notMem_none, *] at h
      all_goals repeat' obtain ⟨_, _, h⟩ := h
      all_goals try dsimp only [Part.some] at *
      all_goals simp_all only [$(mkIdent enc):term, UniqueEncoding.mem_decode_iff]
    · intro h
      subst t
      apply Part.eq_some_iff.mp
      induction $a:ident <;> simp only [$(mkIdent enc):term, $(mkIdent dec):term,
        UniqueEncoding.decode_encode, Part.bind_some, *] <;> rfl)

private def mkInstance (target : Target) (enc dec correct : Name) : TermElabM Command := do
  let header ← mkHeader 0 target
  `(instance $(rootIdent (target.ns ++ `treeEncoding)):ident
      $header.binders:bracketedBinder* : UniqueEncoding Tree $header.targetType :=
    UniqueEncoding.ofDecode $(← header.ref enc) $(← header.ref dec) $(← header.ref correct))

private def codeName (target : Target) (n : Name) : Name :=
  target.ns ++ `Code ++ n

private def mkConstructor (target : Target) (ctor : ConstructorVal) : TermElabM Command := do
  let ind := target.ind
  let name := codeName target ctor.name.getString!.toName
  let args ← (← dataFields ind ctor).mapM fun _ =>
    return mkIdent (← mkFreshUserName `a)
  let binders ← args.mapM fun a => `(bracketedBinder| ($a : Value))
  let shape ← ctorShape ind ctor
  let rhs ← match shape with
    | .nil => ``(pure Value.nil)
    | .field i => ``(pure $(args[i]!))
    | .pair _ _ => do
      let fields ← args.mapM fun a => ``(Value.expression $a)
      let e ← shape.term fields ``Expr.nil ``Expr.pair
      ``(Code.eval $e)
  `(/-- Compute this constructor once from its already evaluated fields. -/
    @[expose, simp] def $(rootIdent name):ident $binders:bracketedBinder* : Code Value := $rhs)

private def mkEncodeEquation (target : Target) (ctor : ConstructorVal) :
    TermElabM Command := do
  let ind := target.ind
  let header ← mkHeader 0 target
  let indices ← indexFields ind ctor
  let headerBinders := header.binders.zipIdx.filterMap fun (b, i) =>
    match target.arguments[i]? with
    | some (some j) =>
      if j < ind.numParams || indices[j - ind.numParams]!.isSome then some b else none
    | _ => some b
  let mut args := #[]
  let mut binders := #[]
  let mut fields := #[]
  for i in [:ctor.numFields] do
    if let some j := indices.idxOf? (some i) then
      args := args.push (mkIdent header.argNames[ind.numParams + j]!)
    else
      let a := mkIdent (← mkFreshUserName `a)
      args := args.push a
      binders := binders.push (← `(bracketedBinder| ($a : _)))
      fields := fields.push a
  let params := (header.argNames.extract 0 ind.numParams).map mkIdent
  let resultIndices ← forallTelescopeReducing ctor.type fun _ result =>
    (result.getAppArgs.extract ind.numParams result.getAppNumArgs).mapIdxM fun j index => do
      if indices[j]!.isSome then return (mkIdent header.argNames[ind.numParams + j]! : Term)
      PrettyPrinter.delab index
  let resultType ← target.app header.parameters (params.map (fun p => (p : Term)) ++ resultIndices)
  let value ← (← ctorShape ind ctor).term fields ``Unit.unit ``Prod.mk
  let rhs ← ``(encode Tree $value)
  let name := target.ns ++ .mkSimple s!"encode_{ctor.name.getString!}"
  -- `dominated` sizes a constructor by its fields, as it sizes a tuple.
  `(@[simp, dominated_simp] theorem $(rootIdent name):ident
      $headerBinders:bracketedBinder* $binders:bracketedBinder* :
    encode Tree (α := $resultType) (@$(mkCIdent ctor.name) $params:term* $args:term*) = $rhs := rfl)

private def Shape.projections : Shape → List (Nat × List Bool)
  | .nil => []
  | .field i => [(i, [])]
  | .pair a b =>
      a.projections.map (fun (i, p) => (i, false :: p)) ++
        b.projections.map (fun (i, p) => (i, true :: p))

private def Shape.sites : Shape → List (List Bool)
  | .field _ => []
  | .nil => [[]]
  | .pair a b => [] :: (a.sites.map (false :: ·) ++ b.sites.map (true :: ·))

private def Shape.nodeAt : Shape → List Bool → Option Bool
  | .nil, [] => some false
  | .pair _ _, [] => some true
  | .pair a b, right :: rest => (if right then b else a).nodeAt rest
  | _, _ => none

private def project (v : Term) (path : List Bool) : TermElabM Term := do
  path.foldlM (init := ← ``(pure $v)) fun p right => do
    if right then ``($p >>= Value.right) else ``($p >>= Value.left)

/-- Inspect only enough of the layout to distinguish constructors, never encoded field data. -/
private partial def dispatch (v : Term) (choices : Array (Shape × Term))
    (returnsValue := false) : TermElabM Term := do
  let some first := choices[0]? | throwError "cannot dispatch an empty type"
  if choices.size = 1 then return first.2
  for path in first.1.sites do
    let nodes := choices.map fun (s, _) => s.nodeAt path
    if nodes.all (·.isSome) && nodes.contains (some true) && nodes.contains (some false) then
      let yes := choices.filter fun (s, _) => s.nodeAt path == some true
      let no := choices.filter fun (s, _) => s.nodeAt path == some false
      let yes ← dispatch v yes returnsValue
      let no ← dispatch v no returnsValue
      if returnsValue then
        let e ← path.foldlM (init := ← ``(Value.expression $v)) fun e right =>
          if right then ``(Expr.right $e) else ``(Expr.left $e)
        return ← ``(Code.branch $e $yes $no)
      return ← ``($(← project v path) >>= fun node => Code.ifNode node $yes $no)
  throwError "constructor layouts cannot be distinguished without inspecting encoded fields"

private def mkCases (target : Target) : TermElabM (Array Command) := do
  let ind := target.ind
  if ind.ctors.isEmpty then return #[]
  let casesName := codeName target `casesOn
  let matchName := codeName target `matchOn
  let v := mkIdent (← mkFreshUserName `v)
  let mut unitBinders := #[]
  let mut valueBinders := #[]
  let mut choices := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let handler := mkIdent (← mkFreshUserName (.mkSimple ctor.name.getString!))
    let mut unitTy ← ``(Code Unit)
    let mut valueTy ← ``(Code Value)
    let mut args : Array Ident := #[]
    for _ in ← dataFields ind ctor do
      unitTy ← ``(Value → $unitTy)
      valueTy ← ``(Value → $valueTy)
      args := args.push (mkIdent (← mkFreshUserName `a))
    unitBinders := unitBinders.push (← `(bracketedBinder| ($handler : $unitTy)))
    valueBinders := valueBinders.push (← `(bracketedBinder| ($handler : $valueTy)))
    let shape ← ctorShape ind ctor
    let paths := (shape.projections.mergeSort (fun a b => a.1 ≤ b.1)).toArray.map (·.2)
    let mut invoke ← `($handler $args:term*)
    for (arg, path) in (args.zip paths).reverse do
      invoke ← ``($(← project v path) >>= fun $arg => $invoke)
    choices := choices.push (shape, invoke)
  let body ← dispatch v choices
  let joinedBody ← dispatch v choices true
  return #[← `(/-- Select a runtime constructor branch, passing its evaluated fields. -/
    @[expose, simp] def $(rootIdent casesName):ident ($v : Value)
      $unitBinders:bracketedBinder* : Code Unit := $body),
    ← `(/-- Select a runtime constructor branch and return its tree value. -/
    @[expose, simp] def $(rootIdent matchName):ident ($v : Value)
      $valueBinders:bracketedBinder* : Code Value := $joinedBody)]

/-- The decision on codes between constructors: tests of the roots of layout nodes, never of
encoded field data. -/
private partial def caseTree (choices : Array (Shape × Term)) : TermElabM Term := do
  let some first := choices[0]? | throwError "cannot dispatch an empty type"
  if choices.size = 1 then return first.2
  for path in first.1.sites do
    let nodes := choices.map fun (s, _) => s.nodeAt path
    if nodes.all (·.isSome) && nodes.contains (some true) && nodes.contains (some false) then
      let yes ← caseTree (choices.filter fun (s, _) => s.nodeAt path == some true)
      let no ← caseTree (choices.filter fun (s, _) => s.nodeAt path == some false)
      return ← ``(CaseTree.test $(quote path) $yes $no)
  throwError "constructor layouts cannot be distinguished without inspecting encoded fields"

/-- The tuple type of a constructor's data fields: dependent pairs where a later field depends on
an earlier one, products otherwise. -/
private def payloadType (u : Level) : List (Lean.Expr × Lean.Expr) → MetaM Lean.Expr
  | [] => return mkConst ``PUnit [.succ u]
  | [(_, t)] => return t
  | (v, t) :: rest => do
    let r ← payloadType u rest
    if r.containsFVar v.fvarId! then mkAppM ``Sigma #[← mkLambdaFVars #[v] r]
    else mkAppM ``Prod #[t, r]

/-- The case view of a type with several constructors: the payload of a constructor is the tuple
of its data fields, which the encoding stores at one subtree. -/
private def mkCaseView (target : Target) : TermElabM (Option Command) := do
  let ind := target.ind
  let k := ind.ctors.length
  if k < 2 then return none
  -- A constructor at a closed index exists at that index only.
  for c in ind.ctors do
    if (← indexFields ind (← getConstInfoCtor c)).any (·.isNone) then return none
  let header ← mkHeader 0 target
  let params := (header.argNames.extract 0 ind.numParams).map mkIdent
  let some payloads ← Term.elabBinders (header.binders.map (·.raw)) fun _ => do
      let T ← instantiateMVars (← Term.elabTerm header.targetType none)
      let .sort (.succ u) ← whnf (← inferType T) | return none
      let source ← withTransparency .default (whnf T)
      let args := source.getAppArgs
      let mut payloads := #[]
      for c in ind.ctors do
        let ctor ← getConstInfoCtor c
        let indices ← indexFields ind ctor
        let data ← dataFields ind ctor
        let ctorType ← instantiateForall (← inferType (mkConst c source.getAppFn.constLevels!))
          (args.extract 0 ind.numParams)
        let some P ← forallTelescopeReducing ctorType fun fs _ => do
            -- Fields fixed by the result indices are the type's indices.
            let fixed := indices.zipIdx.filterMap fun (f, j) =>
              f.map fun f => (fs[f]!, args[ind.numParams + j]!)
            let types ← data.mapM fun i => do
              return (fs[i]!, (← inferType fs[i]!).replaceFVars (fixed.map (·.1)) (fixed.map (·.2)))
            let P ← payloadType u types.toList
            let .sort (.succ v) ← whnf (← inferType P) | return none
            if ← isLevelDefEq u v then return some (P, false)
            -- Fields in a smaller universe are lifted to the type's universe.
            let lifted := mkApp (mkConst ``ULift [u, v]) P
            let .sort (.succ w) ← whnf (← inferType lifted) | return none
            unless ← isLevelDefEq u w do return none
            return some (lifted, true)
          | return none
        payloads := payloads.push (← withOptions (·.setBool `pp.funBinderTypes true) do
          PrettyPrinter.delab P.1, P.2)
      return some payloads
    | return none
  let mut payloadAlts := #[]
  let mut encodingAlts := #[]
  let mut ofPayloadAlts := #[]
  let mut constructorAlts := #[]
  let mut elimAlts := #[]
  let mut rflAlts := #[]
  let mut choices := #[]
  for c in ind.ctors, (P, lifted) in payloads do
    let ctor ← getConstInfoCtor c
    let i := Syntax.mkNumLit (toString ctor.cidx)
    let data ← dataFields ind ctor
    let names ← data.mapM fun _ => return mkIdent (← mkFreshUserName `a)
    let mut tuple ← match names.toList with
      | [] => `(PUnit.unit)
      | [a] => pure a
      | _ => `(⟨$names,*⟩)
    let mut pattern ← match names.toList with
      | [] => `(_)
      | _ => pure tuple
    if lifted then
      tuple ← `(⟨$tuple⟩)
      pattern ← `(⟨$pattern⟩)
    let mut fields : Array Term := #[]
    let mut next := 0
    for j in [:ctor.numFields] do
      if data.contains j then
        fields := fields.push names[next]!
        next := next + 1
      else fields := fields.push (← `(_))
    let underscores ← (List.range ctor.numParams).toArray.mapM fun _ => `(_)
    let value ← `(@$(mkCIdent c):ident $params:term* $fields:term*)
    let ctorPattern ← `(@$(mkCIdent c):ident $underscores:term* $fields:term*)
    payloadAlts := payloadAlts.push (← `(matchAltExpr| | $i:num => $P))
    encodingAlts := encodingAlts.push
      (← `(matchAltExpr| | $i:num => inferInstanceAs (UniqueEncoding Tree $P)))
    ofPayloadAlts := ofPayloadAlts.push (← `(matchAltExpr| | $i:num, $pattern => $value))
    constructorAlts := constructorAlts.push
      (← `(matchAltExpr| | $ctorPattern => ⟨$i:num, $tuple, rfl⟩))
    elimAlts := elimAlts.push (← `(matchAltExpr| | $ctorPattern => g $i:num $tuple h))
    rflAlts := rflAlts.push (← `(matchAltExpr| | $i:num, $pattern => rfl))
    let shape ← ctorShape ind ctor
    -- The fields are the whole code, or the subtree after the tag.
    let path := if shape == fields' data.size then [] else [true]
    choices := choices.push (shape, ← ``(CaseTree.leaf $i:num $(quote path)))
  let dispatch ← caseTree choices
  return some (← `(command|
    instance $(rootIdent (target.ns ++ `caseView)):ident $header.binders:bracketedBinder* :
        CaseView $header.targetType $(Syntax.mkNumLit (toString k)) where
      Payload i := match i with $payloadAlts:matchAlt*
      encoding i := match i with $encodingAlts:matchAlt*
      ofPayload i p := match i, p with $ofPayloadAlts:matchAlt*
      exists_ofPayload t := match t with $constructorAlts:matchAlt*
      elim t g := match (generalizing := false) h : t with $elimAlts:matchAlt*
      elim_ofPayload i p _ := match i, p with $rflAlts:matchAlt*
      dispatch := $dispatch
      select_encode i p := match i, p with $rflAlts:matchAlt*))

/-- The case view of a family whose constructors exist at fixed indices, such as function
symbols by arity, paired with data at the index: `Σ i, T i × R i`. A branch fixes the index, so
data at the index needs no transport. Constructors with fields are not supported. -/
private def mkIndexedCaseView (target : Target) : TermElabM (Option Command) := do
  let ind := target.ind
  let k := ind.ctors.length
  unless k ≥ 2 && ind.numParams == 0 && ind.numIndices == 1 && target.arguments.size == 1 &&
      (← getEnv).contains `Sigma.treeEncoding do
    return none
  let i := mkIdent (← mkFreshUserName `i)
  let family ← target.app #[] #[i]
  let some indexType ← forallTelescopeReducing ind.type fun xs _ => do
      let type ← inferType xs[0]!
      -- The index is stored with the data.
      if (← synthInstance? (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type])).isNone then
        return none
      return some (← PrettyPrinter.delab type)
    | return none
  let mut ofPayloadAlts := #[]
  let mut constructorAlts := #[]
  let mut elimAlts := #[]
  let mut rflAlts := #[]
  let mut payloadAlts := #[]
  let mut encodingAlts := #[]
  let mut choices := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    unless (← dataFields ind ctor).isEmpty do return none
    let some index ← forallTelescopeReducing ctor.type fun _ result => do
        let index := result.getAppArgs[ind.numParams]!
        if index.hasFVar then return none
        return some (← PrettyPrinter.delab index)
      | return none
    let j := Syntax.mkNumLit (toString ctor.cidx)
    let r := mkIdent (← mkFreshUserName `r)
    let value ← `(⟨$index, @$(mkCIdent c):ident, $r⟩)
    payloadAlts := payloadAlts.push (← `(matchAltExpr| | $j:num => R $index))
    encodingAlts := encodingAlts.push
      (← `(matchAltExpr| | $j:num => inferInstanceAs (UniqueEncoding Tree (R $index))))
    ofPayloadAlts := ofPayloadAlts.push (← `(matchAltExpr| | $j:num, $r:ident => $value))
    constructorAlts := constructorAlts.push (← `(matchAltExpr| | $value => ⟨$j:num, $r, rfl⟩))
    elimAlts := elimAlts.push (← `(matchAltExpr| | $value => g $j:num $r h))
    rflAlts := rflAlts.push (← `(matchAltExpr| | $j:num, _ => rfl))
    choices := choices.push (Shape.pair (.field 0) (.pair (← ctorShape ind ctor) (.field 1)),
      ← ``(CaseTree.leaf $j:num [true, true]))
  let dispatch ← caseTree choices
  return some (← `(command|
    instance $(rootIdent (target.ns ++ `caseViewIndexed)):ident {R : $indexType → Type _}
        [∀ i, UniqueEncoding Tree (R i)] :
        CaseView (Σ $i:ident, $family × R $i) $(Syntax.mkNumLit (toString k)) where
      Payload j := match j with $payloadAlts:matchAlt*
      encoding j := match j with $encodingAlts:matchAlt*
      ofPayload j p := match j, p with $ofPayloadAlts:matchAlt*
      exists_ofPayload t := match t with $constructorAlts:matchAlt*
      elim t g := match (generalizing := false) h : t with $elimAlts:matchAlt*
      elim_ofPayload j p _ := match j, p with $rflAlts:matchAlt*
      dispatch := $dispatch
      select_encode j p := match j, p with $rflAlts:matchAlt*))

/-- The code of each field of a structure as a subtree of the structure's code,
`T.encode_field`, by which a field is read. -/
private def mkFieldEquations (target : Target) : TermElabM (Array Command) := do
  let ind := target.ind
  let some info := getStructureInfo? (← getEnv) ind.name | return #[]
  -- Through a type expression, the generated names are not the structure's.
  unless target.ns == privateToUserName ind.name do return #[]
  let ctor ← getConstInfoCtor ind.ctors[0]!
  let data ← dataFields ind ctor
  let header ← mkHeader 1 target
  let x := mkIdent header.targetNames[0]!
  (← ctorShape ind ctor).projections.toArray.mapM fun (j, path) => do
    let field := info.fieldNames[data[j]!]!
    let name := target.ns ++ .mkSimple s!"encode_{field}"
    `(theorem $(rootIdent name):ident $header.binders:bracketedBinder* :
        encode Tree ($(mkCIdent (ind.name ++ field)) $x) = (encode Tree $x).subtree $(quote path) :=
      rfl)

private def deriveOperations (target : Target) (equations := true) : CommandElabM Unit := do
  let ind := target.ind
  withScope (fun sc => { sc with
      levelNames := ind.levelParams ++ sc.levelNames.filter (!ind.levelParams.contains ·) }) do
  let cmds ← liftTermElabM do
    let mut cmds := #[]
    for c in ind.ctors do
      let ctor ← getConstInfoCtor c
      cmds := cmds.push (← mkConstructor target ctor)
      if equations then cmds := cmds.push (← mkEncodeEquation target ctor)
    if equations then cmds := cmds ++ (← mkFieldEquations target)
    let view ← mkCaseView target
    let indexed ← if view.isNone then mkIndexedCaseView target else pure none
    return cmds ++ (← mkCases target) ++ view.toArray ++ indexed.toArray
  for cmd in cmds do elabCommand cmd

private def derive (target : Target) : CommandElabM Unit := do
  let ind := target.ind
  withScope (fun sc => { sc with
      opts := sc.opts.setBool `Elab.async false
      levelNames := ind.levelParams ++ sc.levelNames.filter (!ind.levelParams.contains ·) }) do
    let cmds ← liftTermElabM do
      checkType ind
      checkExisting target
      let enc := target.ns ++ `treeEncode
      let dec := target.ns ++ `treeDecode
      let correct := target.ns ++ `treeDecode_iff
      return #[← mkEncode target enc, ← mkDecode target dec, ← mkCorrect target enc dec correct,
        ← mkInstance target enc dec correct]
    for cmd in cmds do elabCommand cmd
    deriveOperations target

private def nativeTarget (name : Name) : CommandElabM Target := do
  let ind ← getConstInfoInduct name
  return {
    ind, levels := ind.levelParams.map Level.param
    family := mkConst name (ind.levelParams.map Level.param)
    arguments := (Array.range (ind.numParams + ind.numIndices)).map some
    ns := privateToUserName name }

/-- Generate the tree encoding and constructor operations of a first-order inductive type. -/
syntax (name := treeEncodingAttr) "tree_encoding" : attr

initialize registerBuiltinAttribute {
  name := `treeEncodingAttr
  descr := "Generate a unique tree encoding and source constructor operations"
  applicationTime := .afterCompilation
  add := fun name _ kind => do
    unless kind == .global do
      throwError "tree_encoding must be a global attribute"
    liftCommandElabM <| withScope (fun sc => { sc with isPublic := !isPrivateName name }) do
      derive (← nativeTarget name) }

/-- Generate tree encoding and constructor operations in the current namespace.
The expression must expose all parameters and indices of an inductive family.
Definitions are unfolded to inspect its constructors; generated signatures retain
the supplied expression, including types given by structure fields. Non-reducible
aliases of recursive types are not yet supported.
-/
syntax (name := treeEncodingCmd) "tree_encoding " term : command

@[command_elab treeEncodingCmd, inherit_doc treeEncodingCmd]
def elabTreeEncoding : CommandElab := fun stx => do
  let term : Term := ⟨stx[1]⟩
  let (target, levels) ← runTermElabM fun _ => Term.withoutErrToSorry do
    let family ← Term.elabTerm (← `(@($term))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let family ← Term.levelMVarToParam (← instantiateMVars family)
    if family.hasMVar then throwError "Tree encoding needs a fully determined type family"
    let target ← forallTelescopeReducing (← inferType family) fun xs sort => do
      unless sort.isSort && !sort.isProp do
        throwError "Tree encoding expects a data type or a family of data types"
      let target := (mkAppN family xs).headBeta
      let source ← withTransparency .default (whnf target)
      let .const name levels := source.getAppFn |
        throwError "Tree encoding expects an expression reducing to an inductive type"
      let ind ← getConstInfoInduct name
      if ind.isRec && !(← withTransparency .instances (isDefEq target source)) then
        throwError "Tree encoding through a type expression currently supports non-recursive \
          inductive types; recursive aliases also need compatible elimination principles"
      let args := source.getAppArgs
      unless args.all (·.isFVar) && args.toList.eraseDups.length == args.size &&
          xs.all args.contains do
        throwError "Tree encoding expects all inductive parameters and indices to be variables; \
          supply the complete type family"
      let used ← (Lean.collectFVars {} target).addDependencies
      let parameters := (← getLCtx).getFVars.filter fun x => used.fvarSet.contains x.fvarId!
      let arguments := parameters.map args.idxOf?
      let fixed ← ind.ctors.toArray.mapM fun c => do indexFields ind (← getConstInfoCtor c)
      for p in parameters do
        unless args.contains p do
          let ty ← inferType p
          if (args.extract ind.numParams args.size).zipIdx.any fun (arg, i) =>
              fixed.any (·[i]!.isNone) && ty.containsFVar arg.fvarId! then
            throwError "Tree encoding cannot specialize captured parameters depending on \
              fixed indices"
      let family ← mkLambdaFVars parameters target
      return ({ ind, levels, family, arguments, ns := ← getCurrNamespace } : Target)
    return (target, ← Term.getLevelNames)
  withScope (fun sc => { sc with levelNames := (levels ++ sc.levelNames).eraseDups }) do
    derive target

end Complexity.TreeProgram.Deriving

end

public section

run_cmd do
  -- Fields in a smaller universe than their type are lifted, keeping their codes.
  Complexity.TreeProgram.Deriving.derive (← Complexity.TreeProgram.Deriving.nativeTarget ``ULift)
  for name in [``List, ``Option, ``Bool] do
    Complexity.TreeProgram.Deriving.deriveOperations
      (← Complexity.TreeProgram.Deriving.nativeTarget name) false
