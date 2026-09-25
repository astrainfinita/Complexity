/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Analysis.Asymptotics.Basic

/-!
# Asymptotic bounds on natural-number resource functions

`IsBigO f g` uses mathlib's big-O relation after casting the resource functions to
real numbers. Its natural-number criterion allows finite initial exceptions.
-/

@[expose] public section

namespace Complexity

/-- Asymptotic domination of natural-number functions, allowing a constant factor
and finitely many initial exceptions. -/
def IsBigO (f g : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ))

namespace IsBigO

variable {f g h : ℕ → ℕ}

/-- Every resource function bounds itself asymptotically. -/
theorem refl (f : ℕ → ℕ) : IsBigO f f :=
  Asymptotics.isBigO_refl _ _

/-- Asymptotic domination is transitive. -/
theorem trans (hfg : IsBigO f g) (hgh : IsBigO g h) : IsBigO f h :=
  Asymptotics.IsBigO.trans hfg hgh

/-- Big-O bounds on natural resource functions admit a natural constant and
a natural threshold. -/
theorem iff_exists_nat : IsBigO f g ↔
    ∃ c n₀ : ℕ, ∀ n ≥ n₀, f n ≤ c * g n := by
  rw [IsBigO, Asymptotics.isBigO_iff]
  simp only [Real.norm_natCast, Filter.eventually_atTop]
  constructor
  · rintro ⟨c, n₀, h⟩
    obtain ⟨k, hk⟩ := exists_nat_ge c
    refine ⟨k, n₀, fun n hn => ?_⟩
    have h' := (h n hn).trans (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _))
    exact_mod_cast h'
  · rintro ⟨c, n₀, h⟩
    refine ⟨c, n₀, fun n hn => ?_⟩
    exact_mod_cast h n hn

/-- A pointwise upper bound is also an asymptotic upper bound. -/
theorem of_le (h : ∀ n, f n ≤ g n) : IsBigO f g :=
  iff_exists_nat.2 ⟨1, 0, fun n _ => by simpa using h n⟩

end IsBigO

end Complexity
