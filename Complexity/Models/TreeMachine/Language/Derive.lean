/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Complexity.Encoding.Option
public import Complexity.Models.TreeMachine.Language.Verification
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

private def tag : Nat → Shape
  | 0 => .nil
  | n + 1 => .pair .nil (tag n)

private def fields : List Nat → Shape
  | [] => .nil
  | [i] => .field i
  | i :: is => .pair (.field i) (fields is)

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
  `(@[simp] theorem $(rootIdent name):ident
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

private def deriveOperations (target : Target) (equations := true) : CommandElabM Unit := do
  let ind := target.ind
  let cmds ← liftTermElabM do
    let mut cmds := #[]
    for c in ind.ctors do
      let ctor ← getConstInfoCtor c
      cmds := cmds.push (← mkConstructor target ctor)
      if equations then cmds := cmds.push (← mkEncodeEquation target ctor)
    return cmds ++ (← mkCases target)
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
  for name in [``List, ``Option, ``Bool] do
    Complexity.TreeProgram.Deriving.deriveOperations
      (← Complexity.TreeProgram.Deriving.nativeTarget name) false
