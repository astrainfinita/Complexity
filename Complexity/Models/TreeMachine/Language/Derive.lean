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

/-! # Deriving tree representations and source operations

`@[tree_encoding]` generates a unique tree encoding and source operations for a
first-order inductive type. Single-constructor types omit the tag; fixed-arity fields
omit a final list terminator. Constructor fields supplied by the result indices are erased.
-/

public meta section

namespace Complexity.TreeProgram.Deriving

open Lean Parser.Term Meta Elab Deriving Command

private def indexFields (ind : InductiveVal) (ctor : ConstructorVal) : MetaM (Array Nat) :=
  forallTelescopeReducing ctor.type fun xs result => do
    let mut fields := #[]
    for index in result.getAppArgs[ind.numParams...*] do
      let some i := (xs.extract ind.numParams xs.size).idxOf? index |
        throwError "Tree encoding requires constructor result indices to be distinct fields"
      if fields.contains i then
        throwError "Tree encoding requires constructor result indices to be distinct fields"
      fields := fields.push i
    return fields

private def dataFields (ind : InductiveVal) (ctor : ConstructorVal) : MetaM (Array Nat) := do
  let indices ← indexFields ind ctor
  return (List.range ctor.numFields).toArray.filter (!indices.contains ·)

private def withInstances {α : Type} (types : List Lean.Expr) (k : TermElabM α) : TermElabM α :=
  match types with
  | [] => k
  | ty :: types => do
    withLocalDecl (← mkFreshUserName `inst) .instImplicit ty fun _ =>
      withInstances types k

private def explicitBinders : Lean.Expr → Lean.Expr
  | .forallE name ty body _ => .forallE name ty (explicitBinders body) .default
  | .lam name ty body _ => .lam name ty (explicitBinders body) .default
  | e => e

private def encodingRequirements (ind : InductiveVal) : TermElabM (Array Term) :=
  forallBoundedTelescope ind.type ind.numParams fun params _ => do
    let mut requirements := #[]
    for param in params do
      try
        let ty ← mkAppM ``UniqueEncoding #[mkConst ``Tree, param]
        if ← isTypeCorrect ty then requirements := requirements.push ty
      catch _ => pure ()
    for name in ind.ctors do
      let ctor ← getConstInfoCtor name
      let data ← dataFields ind ctor
      let ty ← inferType (mkAppN (mkConst name (ind.levelParams.map Level.param)) params)
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

/-- Bind parameters, indices, and the encodings needed by constructor fields. -/
private def mkHeader (arity : Nat) (ind : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames ind
  let targetType ← mkInductiveApp ind argNames
  let mut binders : Array (TSyntax ``bracketedBinder) :=
    (← mkImplicitBinders argNames).map fun b => ⟨b.raw⟩
  let params := (argNames.extract 0 ind.numParams).map mkIdent
  let instances ← (← encodingRequirements ind).mapM fun requirement =>
    `(bracketedBinder| [($requirement $params:term*)])
  binders := binders ++ instances
  let targetNames ← (List.range arity).toArray.mapM fun _ => mkFreshUserName `x
  for name in targetNames do
    binders := binders.push (← `(bracketedBinder| ($(mkIdent name) : $targetType)))
  return { binders, argNames, targetNames, targetType }

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

private def checkExisting (ind : InductiveVal) : TermElabM Unit := withoutExporting do
  let header ← mkHeader 0 ind
  Term.elabBinders (header.binders.map (·.raw)) fun _ => do
    let ty ← Term.elabTerm header.targetType none
    if (← synthInstance? (← mkAppM ``Encoding #[mkConst ``Tree, ty])).isSome then
      throwError "{privateToUserName ind.name} already has a tree encoding; \
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

private def mkEncode (ind : InductiveVal) (enc : Name) : TermElabM Command := do
  let header ← mkHeader 1 ind
  let discrs ← mkDiscrs header ind
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
        args := args.push (← if ty.isAppOf ind.name then `($(mkIdent enc) $a)
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

private def mkDecode (ind : InductiveVal) (dec : Name) : TermElabM Command := do
  let header ← mkHeader 0 ind
  let params := (header.argNames.extract 0 ind.numParams).map mkIdent
  let mut alts := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let indices ← indexFields ind ctor
    let alt ← forallTelescopeReducing ctor.type fun xs _ => do
      let mut raw := #[]
      let mut values := #[]
      let mut decoded := #[]
      let mut decoders := #[]
      for i in [:ctor.numFields] do
        if let some j := indices.idxOf? i then
          values := values.push (mkIdent header.argNames[ind.numParams + j]!)
          continue
        let r := mkIdent (← mkFreshUserName `r)
        let a := mkIdent (← mkFreshUserName `a)
        raw := raw.push r
        values := values.push a
        decoded := decoded.push a
        let ty ← inferType xs[ctor.numParams + i]!
        decoders := decoders.push (← if ty.isAppOf ind.name then `($(mkIdent dec) $r)
          else ``(decode _ $r))
      let pattern ← (← ctorShape ind ctor).term raw ``Tree.nil ``Tree.pair
      let mut rhs ← ``(Part.some (@$(mkCIdent c) $params:term* $values:term*))
      for i in (List.range decoded.size).reverse do
        let a := decoded[i]!
        rhs ← ``(Part.bind $(decoders[i]!) (fun $a:ident => $rhs))
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

private def mkCorrect (ind : InductiveVal) (enc dec correct : Name) : TermElabM Command := do
  let header ← mkHeader 1 ind
  let a := mkIdent header.targetNames[0]!
  `(theorem $(rootIdent correct):ident $header.binders:bracketedBinder* (t : Tree) :
      $a ∈ $(mkIdent dec) t ↔ $(mkIdent enc) $a = t := by
    induction $a:ident generalizing t <;> unfold $(mkIdent dec):ident <;> try split
    all_goals simp_all [Part.mem_bind_iff, Part.mem_some_iff,
      UniqueEncoding.mem_decode_iff, $(mkIdent enc):term, eq_comm]
    all_goals aesop)

private def mkInstance (ind : InductiveVal) (enc dec correct : Name) : TermElabM Command := do
  let header ← mkHeader 0 ind
  `(instance $(rootIdent (ind.name ++ `treeEncoding)):ident
      $header.binders:bracketedBinder* : UniqueEncoding Tree $header.targetType :=
    UniqueEncoding.ofDecode $(mkIdent enc) $(mkIdent dec) $(mkIdent correct))

private def codeName (ind : InductiveVal) (n : Name) : Name :=
  privateToUserName ind.name ++ `Code ++ n

private def mkConstructor (ind : InductiveVal) (ctor : ConstructorVal) : TermElabM Command := do
  let name := codeName ind ctor.name.getString!.toName
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

private def mkEncodeEquation (ind : InductiveVal) (ctor : ConstructorVal) :
    TermElabM Command := do
  let header ← mkHeader 0 ind
  let indices ← indexFields ind ctor
  let mut args := #[]
  let mut binders := #[]
  let mut encoded := #[]
  for i in [:ctor.numFields] do
    if let some j := indices.idxOf? i then
      args := args.push (mkIdent header.argNames[ind.numParams + j]!)
    else
      let a := mkIdent (← mkFreshUserName `a)
      args := args.push a
      binders := binders.push (← `(bracketedBinder| ($a : _)))
      encoded := encoded.push (← ``(encode Tree $a))
  let params := (header.argNames.extract 0 ind.numParams).map mkIdent
  let rhs ← (← ctorShape ind ctor).term encoded ``Tree.nil ``Tree.pair
  let name := ind.name ++ .mkSimple s!"encode_{ctor.name.getString!}"
  `(@[simp] theorem $(rootIdent name):ident
      $header.binders:bracketedBinder* $binders:bracketedBinder* :
    encode Tree (@$(mkCIdent ctor.name) $params:term* $args:term*) = $rhs := rfl)

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
private partial def dispatch (v : Term) (choices : Array (Shape × Term)) : TermElabM Term := do
  let some first := choices[0]? | throwError "cannot dispatch an empty type"
  if choices.size = 1 then return first.2
  for path in first.1.sites do
    let nodes := choices.map fun (s, _) => s.nodeAt path
    if nodes.all (·.isSome) && nodes.contains (some true) && nodes.contains (some false) then
      let yes := choices.filter fun (s, _) => s.nodeAt path == some true
      let no := choices.filter fun (s, _) => s.nodeAt path == some false
      return ← ``($(← project v path) >>= fun node =>
        Code.ifNode node $(← dispatch v yes) $(← dispatch v no))
  throwError "constructor layouts cannot be distinguished without inspecting encoded fields"

private def mkCases (ind : InductiveVal) : TermElabM (Array Command) := do
  if ind.ctors.isEmpty then return #[]
  let casesName := codeName ind `casesOn
  let matchName := codeName ind `matchOn
  let v := mkIdent (← mkFreshUserName `v)
  let result := mkIdent (← mkFreshUserName `result)
  let mut unitBinders := #[]
  let mut valueBinders := #[]
  let mut choices := #[]
  let mut joined := #[]
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
    let mut branch ← ``(($handler $args:term*) >>= fun a => Code.write $result a)
    for arg in args.reverse do branch ← `(fun $arg => $branch)
    joined := joined.push branch
  let body ← dispatch v choices
  let run ← `($(mkIdent casesName) $v $joined:term*)
  let joinedBody ← if ind.ctors.length = 1 then pure body else
    ``(Code.newVar Value.nil >>= fun $result => $run >>= fun _ => Code.read $result)
  return #[← `(/-- Select a runtime constructor branch, passing its evaluated fields. -/
    @[expose, simp] def $(rootIdent casesName):ident ($v : Value)
      $unitBinders:bracketedBinder* : Code Unit := $body),
    ← `(/-- Select a runtime constructor branch and return its tree value. -/
    @[expose, simp] def $(rootIdent matchName):ident ($v : Value)
      $valueBinders:bracketedBinder* : Code Value := $joinedBody)]

private def deriveOperations (name : Name) (equations := true) : CommandElabM Unit := do
  let ind ← getConstInfoInduct name
  let cmds ← liftTermElabM do
    let mut cmds := #[]
    for c in ind.ctors do
      let ctor ← getConstInfoCtor c
      cmds := cmds.push (← mkConstructor ind ctor)
      if equations then cmds := cmds.push (← mkEncodeEquation ind ctor)
    return cmds ++ (← mkCases ind)
  for cmd in cmds do elabCommand cmd

private def derive (name : Name) : CommandElabM Unit := do
  let ind ← getConstInfoInduct name
  withScope (fun sc => { sc with
      opts := sc.opts.setBool `Elab.async false
      levelNames := ind.levelParams ++ sc.levelNames.filter (!ind.levelParams.contains ·) }) do
    let cmds ← liftTermElabM do
      checkType ind
      checkExisting ind
      let enc := privateToUserName name ++ `treeEncode
      let dec := privateToUserName name ++ `treeDecode
      let correct := privateToUserName name ++ `treeDecode_iff
      return #[← mkEncode ind enc, ← mkDecode ind dec, ← mkCorrect ind enc dec correct,
        ← mkInstance ind enc dec correct]
    for cmd in cmds do elabCommand cmd
    deriveOperations name

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
      derive name }

end Complexity.TreeProgram.Deriving

end

public section

run_cmd Complexity.TreeProgram.Deriving.deriveOperations ``List false
run_cmd Complexity.TreeProgram.Deriving.deriveOperations ``Option false
run_cmd Complexity.TreeProgram.Deriving.deriveOperations ``Bool false
