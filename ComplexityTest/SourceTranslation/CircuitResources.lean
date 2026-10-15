/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Circuit.Program

/-! Public circuit resource proofs, saved growth and structural billing regressions. -/

@[expose] public section

open Complexity
open Complexity.TreeProgram.Source
  (gateClauses gateClauses_size_le accumulateGate accumulateGate_size size_encode_reverse)

namespace ComplexityTest.SourceTranslation.CircuitResources

-- A new algorithm uses ordinary functions and saves its interpretation with an equality.
-- Its model proof supplies clause count and output size, without internal certificates.
def collect (input : CNF ℕ ×
    (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

@[local source] theorem collect_source : collect =
    fun input => (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1 := rfl

open Complexity.TreeProgram.Source in
noncomputable def collectImplementation : Implementation collect :=
  accumulateGateImpl.congr (by funext x; rfl)

open Complexity.TreeProgram.Source in
@[source_growth] theorem collect_growth : collectImplementation.HasGrowth
    (fun _ => 1) (fun input => ⌜input⌝ₜ.size) := by
  source_fun_prop
  all_goals exact Dominated.refl _

@[local source] theorem collect_ftisp : collect ∈ FTISP .tree
    (fun n => n ^ 0) (fun n => n ^ 1) :=
  (by simpa only [pow_zero, pow_one] using collect_growth :
    collectImplementation.HasGrowth (fun x => ⌜x⌝ₜ.size ^ 0)
      (fun x => ⌜x⌝ₜ.size ^ 1)).mem_ftisp_pow (by decide)

-- Pairing reuses the saved growth proof and needs only the genuine output-size relation.
theorem collect_pair_ftisp : (fun input => (collect input, input.1)) ∈ FTISP .tree
    (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  · simp only [pow_zero, Dominated.add_iff]
    repeat' apply And.intro
    all_goals exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  · apply Dominated.of_le_mul 5
    intro input
    have ho := accumulateGate_size input
    change ⌜collect input⌝ₜ.size + 1 = _ at ho
    have hg := gateClauses_size_le input.2
    rcases input with ⟨acc, gate⟩
    simp only [pow_one, size_encode_prod, max_le_iff] at *
    omega

-- Saving growth retains the explicitly chosen program; it does not rebudget it.
open Complexity.TreeProgram.Source in
example : (by source_fun_prop : Implementation collect).program =
    collectImplementation.program := rfl

open Complexity.TreeProgram.Source in
noncomputable def optionalCollectImplementation :
    Implementation (fun input : Option (CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) =>
      match input with | none => [] | some x => collect x) := by
  source_fun_prop

theorem copied_ftisp : collect ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) :=
  collect_ftisp

/-- error: `source` needs an equality or a direct growth-specification exit; it cannot recover a source program from an arbitrary model theorem -/
#guard_msgs in
attribute [local source] copied_ftisp

-- A one-off source choice leaves its ordinary equation and growth comparisons.
example : collect ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop via accumulateGate
  case source_eq => rfl
  all_goals simpa only [pow_zero, pow_one, Function.comp_def] using (Dominated.refl _)

example : True := by
  fail_if_success
    have : collect ∈ FTISP .tree (fun _ => 0) (fun _ => 0) := by
      model_fun_prop
  trivial

-- The peak simplification is an equality, including an empty fold, and does not relax space.
open Complexity.TreeProgram.Source in
example (time : List Bool → Bool → ℕ) (acc xs : List Bool) :
    (foldlCost (fun acc x => x :: acc)
      (fun acc x => ⟨time acc x,
        max (1 + ⌜acc⌝ₜ.size + ⌜x⌝ₜ.size) (1 + ⌜x⌝ₜ.size + ⌜acc⌝ₜ.size)⟩) acc xs).peak + 1 =
      ⌜xs⌝ₜ.size + ⌜acc⌝ₜ.size := by
  rw [foldlCost_prepend_peak]
  simpa using size_encode_list_append xs.reverse acc

-- Ordinary nested calls use saved specifications without choosing a numerical coefficient.
example : accumulateGate ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals simpa only [pow_zero, pow_one, Function.comp_def] using (Dominated.refl _)

example {α : Type*} [UniqueEncoding Tree α] :
    (gateClauses (α := α)) ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals simpa only [pow_zero, pow_one, Function.comp_def] using (Dominated.refl _)

-- Polynomial substitution combines growth, rather than expanding old million-sized budgets.
example {s R : ℕ → ℕ} (hs : Dominated s (fun n => R n ^ 2))
    (hR : ∀ n, 0 < R n) :
    Dominated (fun n => (s n + 1) ^ 3 + R n ^ 2 + 1) (fun n => R n ^ 6) := by
  have h := (hs.add_same (Dominated.one fun n => Nat.pow_pos (hR n))).pow 3
  simp only [← pow_mul] at h
  simp only [Dominated.add_iff]
  exact ⟨⟨h, Dominated.of_le fun n => Nat.pow_le_pow_right (hR n) (by decide)⟩,
    Dominated.one fun n => Nat.pow_pos (hR n)⟩

end ComplexityTest.SourceTranslation.CircuitResources
