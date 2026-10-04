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
omit a final list terminator. Indexed, nested and dependent data need separate support.
-/

public meta section

namespace Complexity.TreeProgram.Deriving

open Lean Parser.Term Meta Elab Deriving Command

/-- Bind the inductive parameters and their encodings in the existing two-parameter class. -/
private def mkHeader (arity : Nat) (ind : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames ind
  let targetType ← mkInductiveApp ind argNames
  let mut binders : Array (TSyntax ``bracketedBinder) :=
    (← mkImplicitBinders argNames).map fun b => ⟨b.raw⟩
  let instances ← forallBoundedTelescope ind.type ind.numParams fun xs _ => do
    let mut instances := #[]
    for i in [:xs.size] do
      try
        let ty ← mkAppM ``UniqueEncoding #[mkConst ``Tree, xs[i]!]
        if (← isTypeCorrect ty) then
          instances := instances.push
            (← `(bracketedBinder| [UniqueEncoding Tree $(mkIdent argNames[i]!)]))
      catch _ => pure ()
    return instances
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

private def ctorShape (ind : InductiveVal) (ctor : ConstructorVal) : Shape :=
  if ind.name == ``List then
    if ctor.cidx = 0 then .nil else .pair (.field 0) (.field 1)
  else if ind.name == ``Option then
    if ctor.cidx = 0 then .nil else .pair .nil (.field 0)
  else if ind.name == ``Bool then
    if ctor.cidx = 0 then .nil else .pair .nil .nil
  else
    let payload := fields (List.range ctor.numFields)
    if ind.ctors.length = 1 then payload else .pair (tag ctor.cidx) payload

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
  if ind.numIndices != 0 || ind.isNested || ind.isReflexive || ind.all.length != 1 then
    throwError "Tree encoding currently supports non-indexed, non-nested, \
      non-mutual first-order inductive types"
  if ind.isRec && ind.ctors.length = 1 then
    throwError "Tree encoding cannot erase the only constructor tag of a recursive type"
  forallTelescopeReducing ind.type fun _ sort => do
    if sort == mkSort .zero then
      throwError "Tree encoding supports data types, not propositions"
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    forallTelescopeReducing ctor.type fun xs _ => do
      for i in [:ctor.numFields] do
        let ty ← whnf (← inferType xs[ctor.numParams + i]!)
        if ty.isForall || (← isProp ty) || ty.isSort then
          throwError "Tree encoding does not support function, proof or type-valued field \
            {xs[ctor.numParams + i]!}"
        for j in [:i] do
          if ty.containsFVar xs[ctor.numParams + j]!.fvarId! then
            throwError "Tree encoding does not yet support dependent constructor fields"

private def mkEncode (ind : InductiveVal) (enc : Name) : TermElabM Command := do
  let header ← mkHeader 1 ind
  let discrs ← mkDiscrs header ind
  let mut alts := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let alt ← forallTelescopeReducing ctor.type fun xs _ => do
      let mut pats : Array Term := Array.replicate ctor.numParams (← `(_))
      let mut args := #[]
      for i in [:ctor.numFields] do
        let a := mkIdent (← mkFreshUserName `a)
        pats := pats.push a
        let ty ← inferType xs[ctor.numParams + i]!
        args := args.push (← if ty.isAppOf ind.name then `($(mkIdent enc) $a)
          else ``(encode Tree $a))
      let rhs ← (ctorShape ind ctor).term args ``Tree.nil ``Tree.pair
      `(matchAltExpr| | @$(mkCIdent c):ident $pats:term* => $rhs)
    alts := alts.push alt
  let body ← `(match $[$discrs],* with $alts:matchAlt*)
  `(/-- The generated structural encoder; use `encode Tree` and its constructor equations. -/
    @[expose] def $(rootIdent enc):ident $header.binders:bracketedBinder* : Tree := $body)

private def mkDecode (ind : InductiveVal) (dec : Name) : TermElabM Command := do
  let header ← mkHeader 0 ind
  let params := header.argNames.map mkIdent
  let mut alts := #[]
  for c in ind.ctors do
    let ctor ← getConstInfoCtor c
    let alt ← forallTelescopeReducing ctor.type fun xs _ => do
      let mut raw := #[]
      let mut values := #[]
      let mut decoders := #[]
      for i in [:ctor.numFields] do
        let r := mkIdent (← mkFreshUserName `r)
        let a := mkIdent (← mkFreshUserName `a)
        raw := raw.push r
        values := values.push a
        let ty ← inferType xs[ctor.numParams + i]!
        decoders := decoders.push (← if ty.isAppOf ind.name then `($(mkIdent dec) $r)
          else ``(decode _ $r))
      let pattern ← (ctorShape ind ctor).term raw ``Tree.nil ``Tree.pair
      let mut rhs ← ``(Part.some (@$(mkCIdent c) $params:term* $values:term*))
      for i in (List.range ctor.numFields).reverse do
        let a := values[i]!
        rhs ← ``(Part.bind $(decoders[i]!) (fun $a:ident => $rhs))
      `(matchAltExpr| | $pattern => $rhs)
    alts := alts.push alt
  let exhaustive ← match ind.ctors with
    | [c] => do pure ((← getConstInfoCtor c).numFields == 1)
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
      UniqueEncoding.mem_decode_iff, $(mkIdent enc):term, eq_comm])

private def mkInstance (ind : InductiveVal) (enc dec correct : Name) : TermElabM Command := do
  let header ← mkHeader 0 ind
  `(instance $(rootIdent (ind.name ++ `treeEncoding)):ident
      $header.binders:bracketedBinder* : UniqueEncoding Tree $header.targetType :=
    UniqueEncoding.ofDecode $(mkIdent enc) $(mkIdent dec) $(mkIdent correct))

private def codeName (ind : InductiveVal) (n : Name) : Name :=
  privateToUserName ind.name ++ `Code ++ n

private def mkConstructor (ind : InductiveVal) (ctor : ConstructorVal) :
    TermElabM (Array Command) := do
  let name := codeName ind ctor.name.getString!.toName
  let args ← (List.range ctor.numFields).toArray.mapM fun _ =>
    return mkIdent (← mkFreshUserName `a)
  let binders ← args.mapM fun a => `(bracketedBinder| ($a : Value))
  let rhs ← (ctorShape ind ctor).term (args.map (⟨·.raw⟩)) ``Value.nil ``Value.pair
  let s := mkIdent (← mkFreshUserName `s)
  let evals ← args.mapM fun a => ``(Value.eval $a $s)
  let tree ← (ctorShape ind ctor).term evals ``Tree.nil ``Tree.pair
  let evalName := codeName ind (.mkSimple s!"eval_{ctor.name.getString!}")
  return #[← `(/-- Build this constructor's tree representation from symbolic field values. -/
    @[expose] def $(rootIdent name):ident $binders:bracketedBinder* : Value := $rhs),
    ← `(@[simp] theorem $(rootIdent evalName):ident
      $binders:bracketedBinder* ($s : ℕ → Tree) :
        ($(mkIdent name) $args:term*).eval $s = $tree := rfl)]

private def mkEncodeEquation (ind : InductiveVal) (ctor : ConstructorVal) :
    TermElabM Command := do
  let header ← mkHeader 0 ind
  let args ← (List.range ctor.numFields).toArray.mapM fun _ =>
    return mkIdent (← mkFreshUserName `a)
  let binders ← args.mapM fun a => `(bracketedBinder| ($a : _))
  let params := header.argNames.map mkIdent
  let encoded ← args.mapM fun a => ``(encode Tree $a)
  let rhs ← (ctorShape ind ctor).term encoded ``Tree.nil ``Tree.pair
  let name := ind.name ++ .mkSimple s!"encode_{ctor.name.getString!}"
  `(@[simp] theorem $(rootIdent name):ident
      $header.binders:bracketedBinder* $binders:bracketedBinder* :
    encode Tree (@$(mkCIdent ctor.name) $params:term* $args:term*) = $rhs := rfl)

private def Shape.projections (s : Shape) (v : Term) : TermElabM (List (Nat × Term)) := do
  match s with
  | .nil => return []
  | .field i => return [(i, v)]
  | .pair a b =>
    return (← a.projections (← ``(Value.left $v))) ++
      (← b.projections (← ``(Value.right $v)))

private def Shape.sites : Shape → List (List Bool)
  | .field _ => []
  | .nil => [[]]
  | .pair a b => [] :: (a.sites.map (false :: ·) ++ b.sites.map (true :: ·))

private def Shape.nodeAt : Shape → List Bool → Option Bool
  | .nil, [] => some false
  | .pair _ _, [] => some true
  | .pair a b, right :: rest => (if right then b else a).nodeAt rest
  | _, _ => none

private def project (v : Term) (path : List Bool) : TermElabM Term :=
  path.foldlM (init := v) fun v right =>
    if right then ``(Value.right $v) else ``(Value.left $v)

/-- Inspect only enough of the layout to distinguish constructors, never encoded field data. -/
private partial def dispatch (v : Term) (choices : Array (Shape × Term)) : TermElabM Term := do
  let some first := choices[0]? | throwError "cannot dispatch an empty type"
  if choices.size = 1 then return first.2
  for path in first.1.sites do
    let nodes := choices.map fun (s, _) => s.nodeAt path
    if nodes.all (·.isSome) && nodes.contains (some true) && nodes.contains (some false) then
      let yes := choices.filter fun (s, _) => s.nodeAt path == some true
      let no := choices.filter fun (s, _) => s.nodeAt path == some false
      return ← ``(Code.ifNode $(← project v path) $(← dispatch v yes) $(← dispatch v no))
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
    for _ in [:ctor.numFields] do
      unitTy ← ``(Value → $unitTy)
      valueTy ← ``(Value → $valueTy)
      args := args.push (mkIdent (← mkFreshUserName `a))
    unitBinders := unitBinders.push (← `(bracketedBinder| ($handler : $unitTy)))
    valueBinders := valueBinders.push (← `(bracketedBinder| ($handler : $valueTy)))
    let shape := ctorShape ind ctor
    let projections ← shape.projections v
    let fields := (projections.mergeSort (fun a b => a.1 ≤ b.1)).toArray.map (·.2)
    choices := choices.push (shape, ← `($handler $fields*))
    let mut branch ← ``(($handler $args:term*) >>= fun a => Code.write $result a)
    for arg in args.reverse do branch ← `(fun $arg => $branch)
    joined := joined.push branch
  let body ← dispatch v choices
  let run ← `($(mkIdent casesName) $v $joined:term*)
  let joinedBody ← if ind.ctors.length = 1 then pure body else
    ``(Code.newVar Value.nil >>= fun $result => $run >>= fun _ => Code.read $result)
  return #[← `(/-- Select a runtime constructor branch, passing its symbolic fields. -/
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
      cmds := cmds ++ (← mkConstructor ind ctor)
      if equations then cmds := cmds.push (← mkEncodeEquation ind ctor)
    return cmds ++ (← mkCases ind)
  for cmd in cmds do elabCommand cmd

private def derive (name : Name) : CommandElabM Unit := do
  let ind ← getConstInfoInduct name
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
