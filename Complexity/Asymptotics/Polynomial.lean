/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial and asymptotic resource bounds

Pointwise natural polynomial bounds and asymptotic bounds by powers describe the
same collection of resource functions. The converse absorbs the finite initial
exceptions into the polynomial's constant coefficient.
-/

@[expose] public section

/-- A polynomial with natural coefficients is monotone on natural inputs. -/
theorem Polynomial.monotone_eval_nat (p : Polynomial ℕ) : Monotone p.eval := by
  intro m n h
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

namespace Complexity

/-- A pointwise shifted power bound gives the corresponding asymptotic power bound. -/
theorem DominatedAtTop.of_le_mul_add_one_pow {f : ℕ → ℕ} (c d : ℕ)
    (h : ∀ n, f n ≤ c * (n + 1) ^ d) : DominatedAtTop f (fun n ↦ n ^ d) := by
  refine dominatedAtTop_iff.2 ⟨c * 2 ^ d, 1, fun n hn ↦ ?_⟩
  calc
    f n ≤ c * (n + 1) ^ d := h n
    _ ≤ c * (2 * n) ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
    _ = c * 2 ^ d * n ^ d := by simp [Nat.mul_pow, Nat.mul_assoc]

/-- A budget indexed by the input size is polynomial at every size exactly when it is eventually
bounded by a power: the constant absorbs the finitely many initial sizes. So polynomial budgets
need no separate eventual notion. -/
theorem isPoly_iff_exists_dominatedAtTop_pow {t : ℕ → ℕ} :
    IsPoly (fun n => n) t ↔ ∃ d, DominatedAtTop t (fun n => n ^ d) := by
  constructor
  · rintro ⟨d, C, h⟩
    exact ⟨d, .of_le_mul_add_one_pow C d fun n => by simpa only [Nat.nsmul_eq_mul] using h n⟩
  · rintro ⟨d, h⟩
    obtain ⟨c, n₀, h⟩ := dominatedAtTop_iff.1 h
    refine ⟨d, c + ∑ n ∈ Finset.range n₀, t n, fun n => ?_⟩
    simp only [Nat.nsmul_eq_mul]
    by_cases hn : n₀ ≤ n
    · calc t n ≤ c * n ^ d := h n hn
        _ ≤ c * (n + 1) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) d)
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · calc t n ≤ ∑ n ∈ Finset.range n₀, t n :=
            Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _)
              (Finset.mem_range.2 (Nat.lt_of_not_ge hn))
        _ ≤ (c + ∑ n ∈ Finset.range n₀, t n) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (Nat.succ_pos n))

/-- A natural polynomial is asymptotically bounded by a power. -/
theorem _root_.Polynomial.exists_dominatedAtTop_pow (p : Polynomial ℕ) :
    ∃ d, DominatedAtTop (fun n => p.eval n) (fun n => n ^ d) := by
  refine ⟨p.natDegree, dominatedAtTop_iff.2 ⟨p.eval 1, 1, fun n hn => ?_⟩⟩
  simp only [Polynomial.eval_eq_sum_range, one_pow, mul_one, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hn (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))

/-- A big-O power bound can be replaced with a polynomial bound at every input
size, including the finite initial exceptions. -/
theorem DominatedAtTop.exists_polynomial_bound {f : ℕ → ℕ} {d : ℕ}
    (h : DominatedAtTop f (fun n => n ^ d)) :
    ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n := by
  obtain ⟨c, n₀, h⟩ := dominatedAtTop_iff.1 h
  refine ⟨Polynomial.C c * Polynomial.X ^ d +
    Polynomial.C (∑ n ∈ Finset.range n₀, f n), fun n => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hn : n₀ ≤ n
  · exact (h n hn).trans (Nat.le_add_right _ _)
  · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2
      (Nat.lt_of_not_ge hn))).trans (Nat.le_add_left _ _)

end Complexity
