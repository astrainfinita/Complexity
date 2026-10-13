/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Circuit.Program

/-! Public circuit resource proofs and the coefficient calculation tried for relabeling. -/

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

-- Internal regression: saving the source retains the original summed fold budget.
open Complexity.TreeProgram.Source in
example : ∃ b, Realizes collect b ∧ ∀ input,
    b.time input = 70 + 16 * (gateClauses input.2).length := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro input
  simp
  omega

open Complexity.TreeProgram.Source in
private noncomputable def rawCollectImplementation : Implementation collect := by
  source_fun_prop

@[local source] theorem collect_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace collect
    (fun _ => 122) (fun n => k * (8 * n + 8)) := by
  model_fun_prop
  all_goals
    rename_i input
    have hg := gateClauses_size_le input.2
    have hl : (gateClauses input.2).length ≤ 3 := CNF.length_ofGate_le _ _ _
    have ha := size_encode_list_append (gateClauses input.2).reverse input.1
    rcases input with ⟨acc, gate⟩
    simp only [size_encode_reverse, size_encode_prod] at *
    omega

-- The model proof saved the compact time/space allowance. Pairing only needs output size.
theorem collect_pair_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun input => (collect input, input.1))
    (fun _ => 201) (fun n => k * (8 * n + 8)) := by
  model_fun_prop
  rename_i input
  have ho := accumulateGate_size input
  change ⌜collect input⌝ₜ.size + 1 = _ at ho
  have hg := gateClauses_size_le input.2
  rcases input with ⟨acc, gate⟩
  simp only [size_encode_prod] at *
  omega

open Complexity.TreeProgram.Source in
example : (by source_fun_prop : Implementation collect).program =
    rawCollectImplementation.program := rfl

-- The generated model-budget certificate also works inside an exposed branch implementation.
open Complexity.TreeProgram.Source in
noncomputable def optionalCollectImplementation :
    Implementation (fun input : Option (CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) =>
      match input with | none => [] | some x => collect x) := by
  source_fun_prop

-- Saving another budget preserves program identity and the original public allowance.
open Complexity.TreeProgram.Source in
example : ∃ b, Realizes collect b ∧ ∀ input, b.time input = 118 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro input
  simp

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace collect
    (fun _ => 200) (fun n => k * (8 * n + 8)) := by
  model_fun_prop

theorem copied_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace collect
    (fun _ => 122) (fun n => k * (8 * n + 8)) := collect_model

/-- error: `source` needs a function equality or a direct `model_fun_prop` proof; it cannot recover a source program from an arbitrary model theorem -/
#guard_msgs in
attribute [local source] copied_model

-- A one-off choice uses the same source, with only its ordinary equation left to prove.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace collect
    (fun _ => 200) (fun n => k * (8 * n + 8)) := by
  model_fun_prop via accumulateGate
  case source_eq => rfl

example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace collect
        (fun _ => 0) (fun n => k * (8 * n + 8)) := by
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

-- These constant witnesses are determined after choosing the saved implementations.
example : ∃ c k, TimeSpaceModel.tree.ComputableInTimeAndSpace accumulateGate
    (fun _ => c) (fun n => k * (8 * n + 8)) := by
  refine ⟨?time, ?model⟩
  case model =>
    model_fun_prop
    exact Nat.le_refl _

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ c k, TimeSpaceModel.tree.ComputableInTimeAndSpace (gateClauses (α := α))
      (fun _ => c) (fun n => k * (4 * n + 2)) := by
  refine ⟨?time, ?model⟩
  case model =>
    model_fun_prop
    exact Nat.le_refl _

-- The local relabel cost estimate needs only powers and linear arithmetic. Its witnesses
-- are uniform over N and s and are calculated from the constituent allowances.
example : ∃ ct cs : ℕ, ∀ N s : ℕ, 1 ≤ N → s ≤ 256 * N ^ 2 →
    1000000 * (s + 1) ^ 3 + 1000 * (128 * N ^ 2 + 1) + 26 ≤ ct * N ^ 6 ∧
    1000000 * (s + 1) ^ 2 ≤ cs * N ^ 4 := by
  refine ⟨1000000 * 257 ^ 3 + 1000 * 129 + 26, 1000000 * 257 ^ 2, ?_⟩
  intro N s hn hs
  have h1 : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hn
  have h26 : N ^ 2 ≤ N ^ 6 := Nat.pow_le_pow_right hn (by decide)
  have h : s + 1 ≤ 257 * N ^ 2 := by omega
  have h2 := pow_le_pow_left' h 2
  have h3 := pow_le_pow_left' h 3
  norm_num [mul_pow, ← pow_mul] at h2 h3 ⊢
  constructor <;> omega

end ComplexityTest.SourceTranslation.CircuitResources
