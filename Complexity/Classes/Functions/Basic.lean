/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Asymptotics.Polynomial

/-! # Function complexity classes

These classes use a model's resource behaviors and input size, independently of
how its computations are represented. The simultaneous class retains one behavior
satisfying both bounds on every valid input code.
-/

@[expose] public section

namespace Complexity

variable {Data α β : Type*} [Encoding Data α] [Encoding Data β]

/-- Functions computable in the given model in time `O(T(n))`. -/
def FTIME (model : TimeSpaceModel Id Data) (T : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t, model.ComputableInTime f t ∧ IsBigO t T}

/-- Functions computable in the given model in space `O(S(n))`. -/
def FSPACE (model : TimeSpaceModel Id Data) (S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ s, model.ComputableInSpace f s ∧ IsBigO s S}

/-- Functions computable by one behavior within both asymptotic bounds. -/
def FTISP (model : TimeSpaceModel Id Data) (T S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t s, model.ComputableInTimeAndSpace f t s ∧ IsBigO t T ∧ IsBigO s S}

/-- Polynomial-time functions between the chosen encoded types. -/
def FP (model : TimeSpaceModel Id Data) : Set (α → β) :=
  ⋃ d : ℕ, FTIME model (fun n => n ^ d)

variable {model : TimeSpaceModel Id Data} {f : α → β} {T S T' S' : ℕ → ℕ}

theorem TimeSpaceModel.ComputableInTime.mem_ftime
    (h : model.ComputableInTime f T) : f ∈ FTIME model T :=
  ⟨T, h, IsBigO.refl T⟩

theorem TimeSpaceModel.ComputableInSpace.mem_fspace
    (h : model.ComputableInSpace f S) : f ∈ FSPACE model S :=
  ⟨S, h, IsBigO.refl S⟩

theorem TimeSpaceModel.ComputableInTimeAndSpace.mem_ftisp
    (h : model.ComputableInTimeAndSpace f T S) : f ∈ FTISP model T S :=
  ⟨T, S, h, IsBigO.refl T, IsBigO.refl S⟩

theorem FTIME.mono (h : IsBigO T T') :
    FTIME (α := α) (β := β) model T ⊆ FTIME model T' := by
  rintro f ⟨t, hf, ht⟩
  exact ⟨t, hf, ht.trans h⟩

theorem FSPACE.mono (h : IsBigO S S') :
    FSPACE (α := α) (β := β) model S ⊆ FSPACE model S' := by
  rintro f ⟨s, hf, hs⟩
  exact ⟨s, hf, hs.trans h⟩

theorem FTISP.mono (ht : IsBigO T T') (hs : IsBigO S S') :
    FTISP (α := α) (β := β) model T S ⊆ FTISP model T' S' := by
  rintro f ⟨t, s, hf, ht₀, hs₀⟩
  exact ⟨t, s, hf, ht₀.trans ht, hs₀.trans hs⟩

theorem FTISP.subset_time :
    FTISP (α := α) (β := β) model T S ⊆ FTIME model T := by
  rintro f ⟨t, s, hf, ht, _⟩
  exact ⟨t, hf.computableInTime, ht⟩

theorem FTISP.subset_space :
    FTISP (α := α) (β := β) model T S ⊆ FSPACE model S := by
  rintro f ⟨t, s, hf, _, hs⟩
  exact ⟨s, hf.computableInSpace, hs⟩

theorem FTISP.subset_inter :
    FTISP (α := α) (β := β) model T S ⊆ FTIME model T ∩ FSPACE model S :=
  fun _ hf => ⟨subset_time hf, subset_space hf⟩

namespace FP

theorem mem_iff_exists_ftime :
    f ∈ FP model ↔ ∃ d : ℕ, f ∈ FTIME model (fun n => n ^ d) :=
  Set.mem_iUnion

/-- Polynomial time admits a polynomial bound valid at every input size. -/
theorem exists_polynomial_bound (h : f ∈ FP model) :
    ∃ p : Polynomial ℕ, model.ComputableInTime f p.eval := by
  obtain ⟨d, t, h, ht⟩ := mem_iff_exists_ftime.mp h
  obtain ⟨p, hp⟩ := ht.exists_polynomial_bound
  exact ⟨p, h.mono hp⟩

/-- A pointwise bound by `c * (n + 1) ^ d` establishes polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : model.ComputableInTime f t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : f ∈ FP model :=
  mem_iff_exists_ftime.mpr ⟨d, t, h, IsBigO.of_le_mul_add_one_pow c d ht⟩

theorem ftime_subset (d : ℕ) :
    FTIME (α := α) (β := β) model (fun n => n ^ d) ⊆ FP model :=
  fun _ hf => mem_iff_exists_ftime.mpr ⟨d, hf⟩

end FP

end Complexity
