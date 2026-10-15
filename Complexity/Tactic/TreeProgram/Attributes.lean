/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.Meta.Tactic.Simp.Attr
public meta import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp.RegisterCommand

public meta section

/-- Project certified budgets before simplifying their source functions. -/
register_simp_attr source_bounds

namespace Complexity.TreeProgram.Source

/-- Function rules tried after structural field extraction; priority only orders rules
within the same stage. This label does not register a `fun_prop` theorem. -/
initialize sourceFallbackAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `source_fallback
    "try this source function rule after structural field extraction"

/-- Explicit source choices take precedence over default lambda implementations.
Mathlib's lambda-rule registry does not retain theorem priorities. -/
initialize sourceSavedImplementationExt : Lean.LabelExtension ← Lean.mkLabelExt

/-- One declared growth specification per named implementation. -/
initialize sourceGrowthExt : Lean.SimpleScopedEnvExtension (Lean.Name × Lean.Name)
    (Std.HashMap Lean.Name (Option Lean.Name)) ←
  Lean.registerSimpleScopedEnvExtension {
    name := `sourceGrowthExt
    initial := {}
    addEntry := fun specs (implementation, theoremName) =>
      -- Separate imports can each register a specification. Retain their conflict instead
      -- of making the caller depend on import order; `none` is not a candidate to try.
      specs.insert implementation (match specs[implementation]? with
        | none => some theoremName
        | some (some previous) => if previous == theoremName then some previous else none
        | some none => none) }

open Lean Meta in
private def growthImplementation (theoremName : Name) : MetaM Name := do
  forallTelescope (← getConstInfo theoremName).type fun _ type => do
    unless type.isAppOfArity `Complexity.TreeProgram.Source.Implementation.HasGrowth 8 do
      throwError "`source_growth` expects a growth specification for a fixed implementation"
    let .const implementation _ := type.getAppArgs[5]!.getAppFn |
      throwError "`source_growth` expects a named implementation"
    return implementation

open Lean Meta in
/-- Register the implementation's declared specification, without a candidate priority. -/
def registerSourceGrowth (theoremName : Name) (kind : AttributeKind) : MetaM Unit := do
  let implementation ← growthImplementation theoremName
  match (sourceGrowthExt.getState (← getEnv))[implementation]? with
  | some (some previous) =>
    unless previous == theoremName do
      throwError "`source_growth` already has a specification for {implementation}: {previous}"
  | some none => throwError "`source_growth` has conflicting imported specifications for {implementation}"
  | none => pure ()
  sourceGrowthExt.add (implementation, theoremName) kind

open Lean Meta in
initialize registerBuiltinAttribute {
  name := `source_growth
  descr := "save the growth specification of a fixed source implementation"
  applicationTime := .afterCompilation
  add := fun theoremName _ kind => MetaM.run' <| registerSourceGrowth theoremName kind
  erase := fun theoremName => MetaM.run' do
    let implementation ← growthImplementation theoremName
    let specs := sourceGrowthExt.getState (← getEnv)
    if specs[implementation]? == some (some theoremName) then
      modifyEnv fun env => sourceGrowthExt.modifyState env fun _ => specs.erase implementation }

open Lean Meta in
/-- Remove local bindings around a model exit without unfolding imported theorem proofs. -/
partial def sourceModelProof (value : Expr) : MetaM Expr := do
  let proof := value.headBeta.consumeMData
  if let .letE _ _ value body _ := proof then
    return ← sourceModelProof (body.instantiate1 value)
  return proof

end Complexity.TreeProgram.Source
