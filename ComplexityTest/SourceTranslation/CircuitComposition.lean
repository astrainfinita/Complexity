/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Resources.Circuit.Unroll
import Complexity.Classes.Functions.Basic
open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.CircuitComposition

def rewire (x : RelabelInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.2.2.1, x.2.1, x.2.2.2.1.relabel x.2.2.2.2⟩
example : ∃ b, Realizes rewire b := ⟨_, by source_fun_prop⟩

def pipeline (x : CompInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1, x.2.2.1, x.2.2.2.1.comp x.2.2.2.2⟩
example : ∃ b, Realizes pipeline b := ⟨_, by source_fun_prop⟩

def preserve (x : Σ n, Σ m, Circuit .booleanAlgebra n m) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.1 + x.2.1, x.2.2.keepInputs⟩
example : ∃ b, Realizes preserve b := ⟨_, by source_fun_prop⟩

def layers (x : Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2, x.1, x.2.1.unroll x.2.2⟩
example : ∃ b, Realizes layers b := ⟨_, by source_fun_prop⟩

/-- Rewiring an already represented set of inputs, retaining the same input count. -/
def rewireStored (x : Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.2.1, x.2.2.1.relabel x.2.2.2⟩

theorem rewireStored_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace rewireStored
      (fun n => 100000000000000000000 * (n + 1) ^ 7)
      (fun n => k * (10000000000000000 * (n + 1) ^ 4)) := by
  model_fun_prop
  all_goals
    rename_i x
    rcases x with ⟨n, m, c, w⟩
    let S := ⌜(n, m, c, w)⌝ₜ.size
    let R := n + m + n + 2 * c.size + 1
    have hc : ⌜c⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have hw : ⌜w⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have hn : n ≤ S := (card_le_size_encode_fin_function w).trans hw
    have hm : m ≤ S := c.outputs_le_size_encode.trans hc
    have hg : c.size ≤ S := c.size_le_size_encode.trans hc
    have hR : R ≤ 5 * (S + 1) := by dsimp only [R]; omega
    have h₂ := pow_le_pow_left' hR 2
    have h₄ := pow_le_pow_left' hR 4
    have h₆ := pow_le_pow_left' hR 6
    norm_num only [mul_pow, Nat.reducePow] at h₂ h₄ h₆
    have hS₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (S + 1)
    have hp₂ : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have hp₄ : (S + 1) ^ 2 ≤ (S + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
    have hp₃₄ : (S + 1) ^ 3 ≤ (S + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
    have hp₇ : 1 ≤ (S + 1) ^ 7 := Nat.one_le_pow 7 _ (by omega)
    have ht : (c.size + 1) * R ^ 6 ≤ 15625 * (S + 1) ^ 7 := calc
      _ ≤ (S + 1) * (15625 * (S + 1) ^ 6) :=
        Nat.mul_le_mul (Nat.add_le_add_right hg 1) h₆
      _ = _ := by rw [pow_succ (S + 1) 6]; ac_rfl
    have hs : (c.size + 1) * (128 * R ^ 2 + 1) ≤ 3201 * (S + 1) ^ 3 := calc
      _ ≤ (S + 1) * (3201 * (S + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.add_le_add_right hg 1) (by omega)
      _ = _ := by rw [pow_succ (S + 1) 2]; ac_rfl
    have hout : ⌜c.relabel w⌝ₜ.size ≤ 400 * (S + 1) ^ 2 := by
      have h := (c.relabel w).size_encode_numeric_le
      simp only [Circuit.size_relabel] at h
      apply h.trans
      have hprod := Nat.mul_le_mul
        (Nat.mul_le_mul_left 100 (by omega : c.size + m + 1 ≤ 2 * (S + 1)))
        (by omega : n + c.size + 1 ≤ 2 * (S + 1))
      convert hprod using 1; ring
    have hncode : ⌜n⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have hmcode : ⌜m⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    simp only [R, S, size_encode_prod, encode_nat_tree, encode_fin_function]
      at hncode hmcode h₂ h₄ ht hs hS₂ hp₂ hp₄ hp₃₄ hp₇ hout
    simp only [Sigma.encode_mk, size_encode_prod, encode_nat_tree,
      encode_fin_function, Nat.mul_assoc, ← max_add_add_right, max_le_iff]
    (repeat' apply And.intro) <;> omega

/-- Unary storage makes the number of generated layers bounded by input size. -/
def layersStored (x : Σ n, Circuit .booleanAlgebra (n + 1) n × List Unit) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2.length, x.1, x.2.1.unroll x.2.2.length⟩

theorem layersStored_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace layersStored
      (fun n => 10 ^ 40 * (n + 1) ^ 20) (fun n => k * (10 ^ 32 * (n + 1) ^ 8)) := by
  model_fun_prop
  all_goals
    rename_i x
    rcases x with ⟨n, step, xs⟩
    let S := ⌜(n, step, xs)⌝ₜ.size
    let N := 2 * n + xs.length + (xs.length + 1) * step.size + 2
    have hs : ⌜step⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have hxs : ⌜xs⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have hn : n ≤ S := step.outputs_le_size_encode.trans hs
    have hg : step.size ≤ S := step.size_le_size_encode.trans hs
    have ht : xs.length ≤ S := (length_le_codeSize xs).trans hxs
    have hprod := Nat.mul_le_mul (Nat.add_le_add_right ht 1) hg
    have hN : N ≤ 2 * (S + 1) ^ 2 := by dsimp [N]; nlinarith only [hn, ht, hprod]
    have h₂ := pow_le_pow_left' hN 2
    have h₄ := pow_le_pow_left' hN 4
    have h₁₀ := pow_le_pow_left' hN 10
    norm_num only [mul_pow, ← pow_mul, Nat.reducePow, Nat.reduceMul] at h₂ h₄ h₁₀
    have hS₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (S + 1)
    have h₁₂ : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have h₂₈ : (S + 1) ^ 2 ≤ (S + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    have h₄₈ : (S + 1) ^ 4 ≤ (S + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    have h₂₂₀ : (S + 1) ^ 2 ≤ (S + 1) ^ 20 := Nat.pow_le_pow_right (by omega) (by decide)
    have ht₂ := pow_le_pow_left' (Nat.add_le_add_right ht 1) 2
    have hstate := size_unrollState_le n step xs.length xs.length le_rfl
    have hout : ⌜step.unroll xs.length⌝ₜ.size ≤ 256 * N ^ 2 := by
      simp only [Sigma.encode_mk, size_encode_prod] at hstate
      dsimp [N]
      omega
    have hncode : ⌜n⌝ₜ.size ≤ S := by simp only [S, size_encode_prod]; omega
    have htcode := size_encode_nat_le xs.length
    have hntcode := size_encode_nat_le (n + xs.length)
    simp only [N, S, size_encode_prod, encode_nat_tree]
      at hs hxs hn ht hncode htcode hntcode h₂ h₄ h₁₀ hS₂ h₁₂ h₂₈ h₄₈ h₂₂₀ ht₂ hout
    simp only [Sigma.encode_mk, size_encode_prod, encode_nat_tree,
      ← max_add_add_right, max_le_iff]
    (repeat' apply And.intro) <;> omega

theorem layersStored_ftisp :
    layersStored ∈ FTISP .tree (fun n => n ^ 20) (fun n => n ^ 8) := by
  obtain ⟨k, hk⟩ := layersStored_model
  exact ⟨_, _, hk, IsBigO.of_le_mul_add_one_pow (10 ^ 40) 20 (fun _ => le_rfl),
    IsBigO.of_le_mul_add_one_pow (k * 10 ^ 32) 8
      (fun _ => by simp only [Nat.mul_assoc, le_refl])⟩

end ComplexityTest.SourceTranslation.CircuitComposition
