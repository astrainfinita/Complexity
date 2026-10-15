/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.Asymptotics
public import ComplexityTest.SourceTranslation.AsymptoticTailRecursion

public import ComplexityTest.SourceTranslation.GrowthConflictLeft
public import ComplexityTest.SourceTranslation.GrowthConflictRight

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
open ComplexityTest.SourceTranslation.Asymptotics

namespace ComplexityTest.SourceTranslation.AsymptoticReuse

-- Exported implementations can inspect the imported certificate without unfolding its evaluator.
noncomputable def importedLoop : Implementation preciseIdentity := by
  source_fun_prop using loop (test := fun _ : List Bool => false)
    (next := preciseIdentity) (finish := preciseIdentity)
    (invariant := fun x y => x = y) (measure := fun _ => 0)
    (step := fun _ => 1) (stop := fun _ => 1) (space := fun x => ⌜x⌝ₜ.size)
  case equation => intro; rfl
  case initial => intro; rfl
  case next_state => intros; contradiction
  case decreases => intros; contradiction
  case input_size => exact Dominated.of_le fun z => by rw [z.2]
  case check_peak =>
    apply Dominated.of_le
    intro z
    have := Tree.size_pos ⌜z.1.2⌝ₜ
    simp only [z.2]
    omega
  case step_peak | stop_peak | step_time | stop_time => exact Dominated.of_le fun _ => Nat.zero_le _
  case check_time => exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  all_goals intro; decide

noncomputable def selected : Implementation (id : List Bool → List Bool) := by source_fun_prop

-- The saved growth theorem belongs to the implementation recovered by source translation.
theorem selected_growth : selected.HasGrowth (fun _ => 0) (fun _ => 0) :=
  identity_ftisp.hasGrowth_sourceImplementation

-- Repeated calls reuse the imported growth specification, at every input.
theorem twice_growth : (selected.comp selected).HasGrowth
    (fun _ => 0 + 0) (fun _ => max 0 0) := by
  source_fun_prop
  all_goals exact Dominated.refl _

-- Coarse exports through an implementation alias also retain zero costs across modules.
noncomputable def aliasSelected : Implementation aliasedIdentity := by source_fun_prop

example : aliasSelected.program = preciseIdentityImplementation.program := by
  simp only [aliasSelected, aliasedIdentity_ftisp.program_sourceImplementation,
    aliasedIdentityImplementation]

example : aliasSelected.HasGrowth (fun _ => 0) (fun _ => 0) :=
  aliasedIdentity_ftisp.hasGrowth_sourceImplementation

example : (aliasSelected.comp aliasSelected).HasGrowth
    (fun _ => 0 + 0) (fun _ => max 0 0) := by
  source_fun_prop
  all_goals exact Dominated.refl _

-- The exact budget is still available; the asymptotic attribute does not rebudget it.
example : selected.bounds = ⟨fun _ => 0, fun _ => 0⟩ := by
  simp only [selected, source_bounds]

open ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drainTwice (xs : List Bool) : List Bool := drain (drain xs)

-- The ordinary model entry recognizes positive powers and reuses the imported loop spec.
-- Neither model overhead nor the loop's callback construction appears in these goals.
@[source] theorem drainTwice_ftisp :
    drainTwice ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    simp only [pow_one, drain, encode_list_nil,
      Dominated.add_iff, Dominated.max_iff]
    exact ⟨Dominated.refl _, Dominated.const_of_pos 1 fun _ => Tree.size_pos _⟩

-- A zero atTop conclusion on a finite type must retain the positive callback specification.
noncomputable def finiteSelected : Implementation Bool.not := by source_fun_prop

example : finiteSelected.program = finiteNotImplementation.program := by
  simp only [finiteSelected, finiteNot_ftisp.program_sourceImplementation]
example : finiteSelected.HasGrowth (fun _ => 1) (fun _ => 1) :=
  finiteNot_ftisp.hasGrowth_sourceImplementation

example : (finiteSelected.comp finiteSelected).HasGrowth
    (fun _ => 1 + 1) (fun _ => max 1 1) := by
  source_fun_prop
  all_goals exact Dominated.refl _

-- Imported duplicates are rejected; neither import order nor structural fallback selects a bound.
/-- error: source budget: conflicting imported specifications for ComplexityTest.SourceTranslation.Asymptotics.importConflictImplementation -/
#guard_msgs in
example : Asymptotics.importConflictImplementation.HasGrowth
    (fun _ => 0) (fun _ => 0) := by source_fun_prop

end ComplexityTest.SourceTranslation.AsymptoticReuse
