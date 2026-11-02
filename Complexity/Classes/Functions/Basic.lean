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

/-- Functions computable in the given model in time `O(T(n))`.
The unrestricted space budget is still uniform over codes of the same size. -/
def FDTIME (model : TimeSpaceModel Id Data) (T : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t, (∃ s, model.ComputableWithinBySize f t s) ∧ DominatedAtTop t T}

/-- Functions computable in the given model in space `O(S(n))`.
The unrestricted time budget is still uniform over codes of the same size. -/
def FDSPACE (model : TimeSpaceModel Id Data) (S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ s, (∃ t, model.ComputableWithinBySize f t s) ∧ DominatedAtTop s S}

/-- Functions computable by one behavior within both asymptotic bounds. -/
def FDTISP (model : TimeSpaceModel Id Data) (T S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t s, model.ComputableWithinBySize f t s ∧
    DominatedAtTop t T ∧ DominatedAtTop s S}

/-- Polynomial-time functions between the chosen encoded types. -/
def FP (model : TimeSpaceModel Id Data) : Set (α → β) :=
  ⋃ d : ℕ, FDTIME model (fun n => n ^ d)

variable {model : TimeSpaceModel Id Data} {f : α → β} {T S T' S' : ℕ → ℕ}

theorem FDTIME.mono (h : DominatedAtTop T T') :
    FDTIME (α := α) (β := β) model T ⊆ FDTIME model T' := by
  rintro f ⟨t, hf, ht⟩
  exact ⟨t, hf, ht.trans h⟩

theorem FDSPACE.mono (h : DominatedAtTop S S') :
    FDSPACE (α := α) (β := β) model S ⊆ FDSPACE model S' := by
  rintro f ⟨s, hf, hs⟩
  exact ⟨s, hf, hs.trans h⟩

theorem FDTISP.mono (ht : DominatedAtTop T T') (hs : DominatedAtTop S S') :
    FDTISP (α := α) (β := β) model T S ⊆ FDTISP model T' S' := by
  rintro f ⟨t, s, hf, ht₀, hs₀⟩
  exact ⟨t, s, hf, ht₀.trans ht, hs₀.trans hs⟩

theorem FDTISP.subset_time :
    FDTISP (α := α) (β := β) model T S ⊆ FDTIME model T := by
  rintro f ⟨t, s, hf, ht, _⟩
  exact ⟨t, ⟨s, hf⟩, ht⟩

theorem FDTISP.subset_space :
    FDTISP (α := α) (β := β) model T S ⊆ FDSPACE model S := by
  rintro f ⟨t, s, hf, _, hs⟩
  exact ⟨s, ⟨t, hf⟩, hs⟩

theorem FDTISP.subset_inter :
    FDTISP (α := α) (β := β) model T S ⊆ FDTIME model T ∩ FDSPACE model S :=
  fun _ hf => ⟨subset_time hf, subset_space hf⟩

namespace TimeSpaceModel

variable {t s : ℕ → ℕ}

/-- Eventual comparisons only relax the budgets; the computation still handles every code. -/
theorem ComputableWithinBySize.mem_fdtisp_of_dominated
    (h : model.ComputableWithinBySize f t s)
    (ht : DominatedAtTop t T) (hs : DominatedAtTop s S) : f ∈ FDTISP model T S :=
  ⟨t, s, h, ht, hs⟩

theorem ComputableWithinBySize.mem_fdtime_of_dominated
    (h : model.ComputableWithinBySize f t s)
    (ht : DominatedAtTop t T) : f ∈ FDTIME model T :=
  ⟨t, ⟨s, h⟩, ht⟩

theorem ComputableWithinBySize.mem_fdspace_of_dominated
    (h : model.ComputableWithinBySize f t s)
    (hs : DominatedAtTop s S) : f ∈ FDSPACE model S :=
  ⟨s, ⟨t, h⟩, hs⟩

/-- Export the same behavior with both actual-code-size budgets. -/
theorem ComputableWithinBySize.mem_fdtisp
    (h : model.ComputableWithinBySize f t s) : f ∈ FDTISP model t s :=
  h.mem_fdtisp_of_dominated (DominatedAtTop.refl _) (DominatedAtTop.refl _)

theorem ComputableWithinBySize.mem_fdtime
    (h : model.ComputableWithinBySize f t s) : f ∈ FDTIME model t :=
  h.mem_fdtime_of_dominated (DominatedAtTop.refl _)

theorem ComputableWithinBySize.mem_fdspace
    (h : model.ComputableWithinBySize f t s) : f ∈ FDSPACE model s :=
  h.mem_fdspace_of_dominated (DominatedAtTop.refl _)

end TimeSpaceModel

namespace FP

theorem mem_iff_exists_fdtime :
    f ∈ FP model ↔ ∃ d : ℕ, f ∈ FDTIME model (fun n => n ^ d) :=
  Set.mem_iUnion

/-- Polynomial time admits a polynomial bound valid at every input size. -/
theorem exists_polynomial_bound (h : f ∈ FP model) :
    ∃ (p : Polynomial ℕ) (s : ℕ → ℕ), model.ComputableWithinBySize f p.eval s := by
  obtain ⟨d, t, ⟨s, h⟩, ht⟩ := mem_iff_exists_fdtime.mp h
  obtain ⟨p, hp⟩ := ht.exists_polynomial_bound
  exact ⟨p, s, h.mono hp (fun _ => le_rfl)⟩

/-- A pointwise comparison with a polynomial preserves polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : f ∈ FDTIME model t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : f ∈ FP model :=
  mem_iff_exists_fdtime.mpr ⟨d, FDTIME.mono (DominatedAtTop.of_le_mul_add_one_pow c d ht) h⟩

theorem fdtime_subset (d : ℕ) :
    FDTIME (α := α) (β := β) model (fun n => n ^ d) ⊆ FP model :=
  fun _ hf => mem_iff_exists_fdtime.mpr ⟨d, hf⟩

end FP

end Complexity

namespace Complexity.TimeSpaceModel

variable {Data α β : Type*} [UniqueEncoding Data α] [Encoding Data β]
  {model : TimeSpaceModel Id Data} {f : α → β} {T S : ℕ → ℕ}

/-- A size-indexed specialization of an all-input certificate reaches the complexity boundary. -/
theorem ComputableWithin.mem_fdtisp
    (h : model.ComputableWithin f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a)))) : f ∈ FDTISP model T S :=
  (ComputableWithin.iff_bySize.mp h).mem_fdtisp

/-- Export the same machine; an eventual class conclusion is never used as a call specification. -/
theorem ComputableInO.mem_fdtisp
    (h : model.ComputableInO f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a)))) : f ∈ FDTISP model T S := by
  obtain ⟨t, s, h, ⟨C, ht⟩, ⟨D, hs⟩⟩ := h
  exact FDTISP.mono ((Dominated.refl T).const_mul_left C).atTop
    ((Dominated.refl S).const_mul_left D).atTop (h.mono ht hs).mem_fdtisp

end Complexity.TimeSpaceModel
