/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Mathlib.Analysis.Asymptotics.Basic

/-! # Natural-valued domination and real-valued big-O

This optional module relates `DominatedAtTop` to `Asymptotics.IsBigO` after casting to the reals.
The basic domination calculus does not import real numbers or normed spaces.
-/

@[expose] public section

namespace Complexity

/-- Domination at infinity of natural-valued sequences is equivalent to big-O at infinity
after casting their values to the reals. -/
theorem dominatedAtTop_iff_isBigO_natCast {f g : ℕ → ℕ} : DominatedAtTop f g ↔
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) := by
  rw [dominatedAtTop_iff, Asymptotics.isBigO_iff]
  simp only [Real.norm_natCast, Filter.eventually_atTop]
  constructor
  · rintro ⟨c, n₀, h⟩
    refine ⟨c, n₀, fun n hn => ?_⟩
    exact_mod_cast h n hn
  · rintro ⟨c, n₀, h⟩
    obtain ⟨k, hk⟩ := exists_nat_ge c
    refine ⟨k, n₀, fun n hn => ?_⟩
    have h' := (h n hn).trans (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _))
    exact_mod_cast h'

end Complexity
