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

-- A new algorithm uses ordinary functions and saves an explicitly chosen implementation.
-- Its model proof supplies clause count and output size, without internal certificates.
def collect (input : CNF ℕ ×
    (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

open Complexity.TreeProgram.Source in
@[local program] theorem hasProgramIn_collect :
    HasProgramIn collect programAccumulateGate IsO(fun _ => 1) IsO(fun input => ⌜input⌝ₜ.size) :=
  hasProgramIn_accumulateGate.congr (by funext x; rfl)

theorem collect_fdtisp : collect ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

-- Pairing reuses the selected growth and needs only the genuine output-size relation.
theorem collect_pair_fdtisp : (fun input => (collect input, input.1)) ∈ FDTISP .tree
    (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  · apply Dominated.of_le_mul 5
    intro input
    have ho := accumulateGate_size input
    change ⌜collect input⌝ₜ.size + 1 = _ at ho
    have hg := gateClauses_size_le input.2
    rcases input with ⟨acc, gate⟩
    simp only [pow_one, size_encode_prod, max_le_iff] at *
    omega

-- The selected program is reused as chosen.
open Complexity.TreeProgram.Source in
open Complexity.TreeProgram.Source.Internal (HasProgram) in
example := (by source_fun_prop : HasProgram collect programAccumulateGate _ _)

open Complexity.TreeProgram.Source in
open Complexity.TreeProgram.Source.Internal (HasProgram) in
example : True := by
  have := (by source_fun_prop : HasProgram (fun input : Option (CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) =>
      match input with | none => [] | some x => collect x) _ _ _)
  trivial

theorem copied_fdtisp : collect ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) :=
  collect_fdtisp

/-- error: `program` expects a function equality or a named implementation -/
#guard_msgs in
attribute [local program] copied_fdtisp

-- A one-off source choice leaves its ordinary equation and growth comparisons.
example : collect ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop via accumulateGate
  case source_eq => rfl

example : True := by
  fail_if_success
    have : collect ∈ FDTISP .tree (fun _ => 0) (fun _ => 0) := by
      model_fun_prop
  trivial

-- The peak of prepending is the final list's size, including an empty fold.
open Complexity.TreeProgram.Source in
open Complexity.TreeProgram.Source.Internal (HasProgram) in
example (acc xs : List Bool) :
    foldlPeak (fun acc x => x :: acc) (fun z => ⌜z⌝ₜ.size) acc xs + 1 =
      ⌜xs⌝ₜ.size + ⌜acc⌝ₜ.size := by
  have := Tree.size_pos ⌜xs⌝ₜ
  rw [foldlPeak_prepend]
  omega

-- Ordinary nested calls use saved specifications without choosing a numerical coefficient.
example : accumulateGate ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    gateClauses (α := α) ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

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
