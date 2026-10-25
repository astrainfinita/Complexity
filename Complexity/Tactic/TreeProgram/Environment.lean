/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.Meta

public meta section

namespace Complexity.TreeProgram.Source.Environment
open Lean Meta

/-- Normalize source data projections, preserving type families and class interfaces. -/
def normalizeProjections (e : Lean.Expr) (only? : Option FVarId := none) : MetaM Lean.Expr :=
  transform e (post := fun e => do
    if let some id := only? then
      unless e.containsFVar id do return .done e
    let mut reduced := e.headBeta
    let dataProjection ← (show MetaM Bool from do match reduced with
      | .proj name .. => pure (!(isClass (← getEnv) name))
      | _ => do
        let some name := reduced.getAppFn.constName? | return false
        let some info ← getProjectionFnInfo? name | return false
        return !info.fromClass && reduced.getAppNumArgs > info.numParams)
    if dataProjection then
      let typeFormer ← forallTelescopeReducing (← inferType reduced) fun _ result =>
        pure result.isSort
      unless typeFormer do
        let value ← whnf reduced
        unless value.isProj do reduced := value
    return if reduced == e then .done e else .visit reduced)

private partial def withFields {α : Type} (ty source : Lean.Expr)
    (k : Lean.Expr → Array (Lean.Expr × Lean.Expr) → MetaM α) : MetaM α := do
  let reduced ← normalizeProjections (← whnf ty)
  let name := reduced.getAppFn.constName?
  if name == some ``Prod || name == some ``Sigma then
    let name := name.get!
    let #[a, b] := reduced.getAppArgs | throwError "bad structure"
    withFields a (.proj name 0 source) fun left ls => do
      let rightTy := if name == ``Sigma then b.beta #[left] else b
      withFields rightTy (.proj name 1 source) fun right rs => do
        let value ← mkAppOptM (name ++ `mk) #[some a, some b, some left, some right]
        k value (ls ++ rs)
  -- A field keeps its declared type, whose instances are found by its name.
  else withLocalDeclD `field (← normalizeProjections ty) fun value => k value #[(value, source)]

/-- The value and its projections are computed together, including erased proof fields. -/
structure Packed where
  value : Lean.Expr
  unpack : Lean.Expr → MetaM (Array Lean.Expr)

/-- Close a telescope using products, dependent pairs, and proof-erasing subtypes. -/
partial def packValues (xs : List Lean.Expr) : MetaM Packed := do
  match xs with
  | [] => return ⟨mkConst ``Unit.unit, fun _ => pure #[]⟩
  | x :: xs =>
    let originalType ← inferType x
    let xty ← normalizeProjections originalType
    let value ← if xty == originalType then pure x else mkAppOptM ``id #[some xty, some x]
    if xs.isEmpty && !(← isProp xty) then
      return ⟨value, fun value => pure #[value]⟩
    let rest ← packValues xs
    let ty ← normalizeProjections (← inferType rest.value)
    if ← isProp xty then
      let ty ← normalizeProjections ty x.fvarId!
      if ty.containsFVar x.fvarId! then
        throwError (.tagged `sourceCandidateFailure
          "source environment: a runtime field's type depends on a proof")
      let predicate ← withLocalDeclD `data ty fun data => mkLambdaFVars #[data] xty
      let value ← mkAppOptM ``Subtype.mk #[some ty, some predicate, some rest.value, some value]
      return ⟨value, fun value => do
        return #[← mkAppM ``Subtype.property #[value]] ++
          (← rest.unpack (← mkAppM ``Subtype.val #[value]))⟩
    let dependent := ty.containsFVar x.fvarId!
    let value ← if dependent then
      mkAppOptM ``Sigma.mk #[some xty,
        some (← normalizeProjections (← mkLambdaFVars #[x] ty)), some value, some rest.value]
      else mkAppM ``Prod.mk #[value, rest.value]
    let name := if dependent then ``Sigma else ``Prod
    return ⟨value, fun value => do
      return #[← mkAppM (name ++ `fst) #[value]] ++
        (← rest.unpack (← mkAppM (name ++ `snd) #[value]))⟩

/-- Factor a function through its used product/sigma fields and their type dependencies.
Returns `(outer, inner)` with `outer ∘ inner` definitionally equal to the original function.
No-op decompositions are rejected; ordinary function decomposition should be tried first. -/
def decomposition? (fn : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let .forallE _ inputType _ _ ← whnf (← inferType fn) | return none
  withLocalDeclD `input inputType fun input =>
    withFields inputType input fun rebuilt fields => do
      let body ← whnf (fn.beta #[rebuilt])
      let body ← normalizeProjections body
      let mut used := collectFVars {} body
      for (v, _) in fields.reverse do
        if used.fvarSet.contains v.fvarId! then
          used := collectFVars used (← inferType v)
      let usedFields := fields.filter fun (v, _) => used.fvarSet.contains v.fvarId!
      let vars := usedFields.map Prod.fst
      let packed ← packValues vars.toList
      let outer ← withLocalDeclD `env (← inferType packed.value) fun env => do
        let body ← mkLambdaFVars vars body
        mkLambdaFVars #[env] (body.beta (← packed.unpack env))
      let packed := packed.value.replace fun e =>
        (usedFields.find? fun (v, _) => v == e).map Prod.snd
      let inner ← mkLambdaFVars #[input] packed
      if ← isDefEq fn outer then return none
      if ← isDefEq fn inner then return none
      -- The result's type may depend on the environment.
      let composite ← withLocalDeclD `x (← inferType input) fun x => do
        mkLambdaFVars #[x] (mkApp outer (mkApp inner x)).headBeta
      unless ← isDefEq fn composite do return none
      return some (outer, inner)

end Complexity.TreeProgram.Source.Environment
