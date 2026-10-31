/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Cost
public import Mathlib.Algebra.BigOperators.Fin

/-! # Embedding tree registers into a larger empty bank -/

@[expose] public section

namespace Complexity.TreeMachine

variable {k r : ℕ}

/-- Keep the original register indices and fill the remaining registers with `nil`. -/
def pad (_h : k ≤ r) (ρ : Fin k → Tree) (j : Fin r) : Tree :=
  if hj : j.val < k then ρ ⟨j.val, hj⟩ else .nil

@[simp] theorem pad_get (h : k ≤ r) (ρ : Fin k → Tree) (i : Fin k) :
    pad h ρ (Fin.castLE h i) = ρ i := by
  simp [pad]

@[simp] theorem pad_comp_castLE (h : k ≤ r) (ρ : Fin k → Tree) :
    pad h ρ ∘ Fin.castLE h = ρ := by
  funext i
  exact pad_get h ρ i

theorem pad_of_le (h : k ≤ r) (ρ : Fin k → Tree) (j : Fin r) (hj : k ≤ j.val) :
    pad h ρ j = .nil := by
  simp [pad, Nat.not_lt.mpr hj]

@[simp] theorem pad_self (ρ : Fin k → Tree) : pad le_rfl ρ = ρ := by
  funext i
  simp [pad]

@[simp] theorem pad_nil (h : k ≤ r) :
    pad h (fun _ => .nil) = (fun _ => .nil) := by
  funext j
  simp [pad]

theorem pad_update (h : k ≤ r) (ρ : Fin k → Tree) (i : Fin k) (a : Tree) :
    pad h (Function.update ρ i a) = Function.update (pad h ρ) (Fin.castLE h i) a := by
  funext j
  by_cases hj : j.val < k
  · simp [pad, hj, Function.update_apply, Fin.ext_iff]
  · have hji : j ≠ Fin.castLE h i := by
      intro he
      subst j
      exact hj i.isLt
    simp [pad, hj, hji]

@[simp] theorem pad_input (h : k ≤ r) (i : Fin k) (a : Tree) :
    pad h (input i a) = input (Fin.castLE h i) a := by
  simp only [input, pad_update, pad_nil]

/-- Executing an embedded instruction preserves every added empty register. -/
theorem pad_eval (h : k ≤ r) (ρ : Fin k → Tree) (o : Action k) :
    (o.rename (Fin.castLE h)).eval (pad h ρ) = pad h (o.eval ρ) := by
  cases o <;> simp [Action.rename, Action.eval, pad_update]

/-- Each additional empty register contributes one node to space. -/
theorem sum_size_pad (h : k ≤ r) (ρ : Fin k → Tree) :
    (∑ j, (pad h ρ j).size) = (∑ i, (ρ i).size) + (r - k) := by
  induction r with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ r ih =>
      by_cases hk : k = r + 1
      · subst k
        simp
      · have hkr : k ≤ r := by omega
        rw [Fin.sum_univ_castSucc]
        have hs : (∑ j : Fin r, (pad h ρ j.castSucc).size) =
            ∑ j : Fin r, (pad hkr ρ j).size := rfl
        rw [hs, ih hkr]
        have hn : ¬r < k := by omega
        simp only [pad, Fin.val_last, dite_eq_right hn, Tree.size_nil]
        omega

end Complexity.TreeMachine
