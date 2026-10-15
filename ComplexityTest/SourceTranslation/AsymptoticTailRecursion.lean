/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drain (_ : List Bool) : List Bool := []

noncomputable def drainImplementation : Implementation drain := by
  source_fun_prop using loop (test := fun xs : List Bool => !xs.isEmpty)
    (next := List.tail) (finish := id)
    (invariant := fun xs ys : List Bool => ys.length ≤ xs.length ∧ ⌜ys⌝ₜ.size ≤ ⌜xs⌝ₜ.size)
    (measure := List.length) (step := fun _ => 1) (stop := fun _ => 1)
    (space := fun xs => ⌜xs⌝ₜ.size)
  case equation => intro xs; cases xs <;> rfl
  case initial => exact fun _ => ⟨le_rfl, le_rfl⟩
  case next_state =>
    intro xs ys hi _
    cases ys <;> simp_all [encode_list_cons, size_encode_prod]
    omega
  case decreases => intro xs ys _ ht; cases ys <;> simp_all
  case input_size => exact Dominated.of_le fun z => z.2.2
  case check_peak => exact Dominated.of_le fun z => z.2.2
  case step_peak => exact Dominated.of_le fun z => z.2.2
  case stop_peak => exact Dominated.of_le fun _ => Nat.zero_le _
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact Dominated.of_le fun _ => Nat.zero_le _
  all_goals intro; decide

-- Neither callback budgets nor a chosen credit coefficient occur in this proof.
@[source_growth] theorem drain_growth : drainImplementation.HasGrowth
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  · simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated (List.length : List Bool → ℕ) (fun xs => ⌜xs⌝ₜ.size) :=
      Dominated.of_le length_le_codeSize
    have hc (n : ℕ) : Dominated (fun _ : List Bool => n) (fun xs => ⌜xs⌝ₜ.size) :=
      Dominated.const_of_pos n fun _ => Tree.size_pos _
    exact ⟨⟨hc 1, ⟨h, hc 1⟩⟩, hc 4⟩
  · exact Dominated.refl _

@[source] theorem drain_ftisp : drain ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) :=
  (by simpa only [pow_one] using drain_growth :
    drainImplementation.HasGrowth (fun xs => ⌜xs⌝ₜ.size ^ 1) (fun xs => ⌜xs⌝ₜ.size ^ 1)).mem_ftisp_pow
      (by decide)

-- The program is determined by the callbacks; tail-loop space has no stack multiplier.
example : drainImplementation.program =
    loopCode (Implementation.listNonempty (α := Bool)).program
      (Implementation.listTail (α := Bool)).program
      (Implementation.identity (α := List Bool)).program := by
  rfl

end ComplexityTest.SourceTranslation.AsymptoticTailRecursion
