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

namespace TimeSpaceModel

/-- Budgets at the complexity boundary depend on the size of the actual input code.
This does not require unique encodings or assign a canonical size to an abstract value. -/
def ComputableWithSizeBudgets (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : ℕ → ℕ) : Prop :=
  model.ComputableWithCodeBudgets f
    (fun _ src => t (model.inputSize src))
    (fun _ src => s (model.inputSize src))

theorem ComputableWithSizeBudgets.mono {model : TimeSpaceModel Id Data}
    {f : α → β} {t s t' s' : ℕ → ℕ}
    (h : model.ComputableWithSizeBudgets f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    model.ComputableWithSizeBudgets f t' s' :=
  ComputableWithCodeBudgets.mono h (fun _ r => ht (model.inputSize r))
    (fun _ r => hs (model.inputSize r))

end TimeSpaceModel

/-- Functions computable in the given model in time `O(T(n))`.
The unrestricted space budget is still uniform over codes of the same size. -/
def FTIME (model : TimeSpaceModel Id Data) (T : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t, (∃ s, model.ComputableWithSizeBudgets f t s) ∧ DominatedAtTop t T}

/-- Functions computable in the given model in space `O(S(n))`.
The unrestricted time budget is still uniform over codes of the same size. -/
def FSPACE (model : TimeSpaceModel Id Data) (S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ s, (∃ t, model.ComputableWithSizeBudgets f t s) ∧ DominatedAtTop s S}

/-- Functions computable by one behavior within both asymptotic bounds. -/
def FTISP (model : TimeSpaceModel Id Data) (T S : ℕ → ℕ) : Set (α → β) :=
  {f | ∃ t s, model.ComputableWithSizeBudgets f t s ∧
    DominatedAtTop t T ∧ DominatedAtTop s S}

/-- Polynomial-time functions between the chosen encoded types. -/
def FP (model : TimeSpaceModel Id Data) : Set (α → β) :=
  ⋃ d : ℕ, FTIME model (fun n => n ^ d)

variable {model : TimeSpaceModel Id Data} {f : α → β} {T S T' S' : ℕ → ℕ}

theorem FTIME.mono (h : DominatedAtTop T T') :
    FTIME (α := α) (β := β) model T ⊆ FTIME model T' := by
  rintro f ⟨t, hf, ht⟩
  exact ⟨t, hf, ht.trans h⟩

theorem FSPACE.mono (h : DominatedAtTop S S') :
    FSPACE (α := α) (β := β) model S ⊆ FSPACE model S' := by
  rintro f ⟨s, hf, hs⟩
  exact ⟨s, hf, hs.trans h⟩

theorem FTISP.mono (ht : DominatedAtTop T T') (hs : DominatedAtTop S S') :
    FTISP (α := α) (β := β) model T S ⊆ FTISP model T' S' := by
  rintro f ⟨t, s, hf, ht₀, hs₀⟩
  exact ⟨t, s, hf, ht₀.trans ht, hs₀.trans hs⟩

theorem FTISP.subset_time :
    FTISP (α := α) (β := β) model T S ⊆ FTIME model T := by
  rintro f ⟨t, s, hf, ht, _⟩
  exact ⟨t, ⟨s, hf⟩, ht⟩

theorem FTISP.subset_space :
    FTISP (α := α) (β := β) model T S ⊆ FSPACE model S := by
  rintro f ⟨t, s, hf, _, hs⟩
  exact ⟨s, ⟨t, hf⟩, hs⟩

theorem FTISP.subset_inter :
    FTISP (α := α) (β := β) model T S ⊆ FTIME model T ∩ FSPACE model S :=
  fun _ hf => ⟨subset_time hf, subset_space hf⟩

namespace TimeSpaceModel

variable {t s : ℕ → ℕ}

/-- Eventual comparisons only relax the budgets; the computation still handles every code. -/
theorem ComputableWithSizeBudgets.mem_ftisp_of_dominated
    (h : model.ComputableWithSizeBudgets f t s)
    (ht : DominatedAtTop t T) (hs : DominatedAtTop s S) : f ∈ FTISP model T S :=
  ⟨t, s, h, ht, hs⟩

theorem ComputableWithSizeBudgets.mem_ftime_of_dominated
    (h : model.ComputableWithSizeBudgets f t s)
    (ht : DominatedAtTop t T) : f ∈ FTIME model T :=
  ⟨t, ⟨s, h⟩, ht⟩

theorem ComputableWithSizeBudgets.mem_fspace_of_dominated
    (h : model.ComputableWithSizeBudgets f t s)
    (hs : DominatedAtTop s S) : f ∈ FSPACE model S :=
  ⟨s, ⟨t, h⟩, hs⟩

/-- Export the same behavior with both actual-code-size budgets. -/
theorem ComputableWithSizeBudgets.mem_ftisp
    (h : model.ComputableWithSizeBudgets f t s) : f ∈ FTISP model t s :=
  h.mem_ftisp_of_dominated (DominatedAtTop.refl _) (DominatedAtTop.refl _)

theorem ComputableWithSizeBudgets.mem_ftime
    (h : model.ComputableWithSizeBudgets f t s) : f ∈ FTIME model t :=
  h.mem_ftime_of_dominated (DominatedAtTop.refl _)

theorem ComputableWithSizeBudgets.mem_fspace
    (h : model.ComputableWithSizeBudgets f t s) : f ∈ FSPACE model s :=
  h.mem_fspace_of_dominated (DominatedAtTop.refl _)

end TimeSpaceModel

namespace FP

theorem mem_iff_exists_ftime :
    f ∈ FP model ↔ ∃ d : ℕ, f ∈ FTIME model (fun n => n ^ d) :=
  Set.mem_iUnion

/-- Polynomial time admits a polynomial bound valid at every input size. -/
theorem exists_polynomial_bound (h : f ∈ FP model) :
    ∃ (p : Polynomial ℕ) (s : ℕ → ℕ), model.ComputableWithSizeBudgets f p.eval s := by
  obtain ⟨d, t, ⟨s, h⟩, ht⟩ := mem_iff_exists_ftime.mp h
  obtain ⟨p, hp⟩ := ht.exists_polynomial_bound
  exact ⟨p, s, h.mono hp (fun _ => le_rfl)⟩

/-- A pointwise comparison with a polynomial preserves polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : f ∈ FTIME model t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : f ∈ FP model :=
  mem_iff_exists_ftime.mpr ⟨d, FTIME.mono (DominatedAtTop.of_le_mul_add_one_pow c d ht) h⟩

theorem ftime_subset (d : ℕ) :
    FTIME (α := α) (β := β) model (fun n => n ^ d) ⊆ FP model :=
  fun _ hf => mem_iff_exists_ftime.mpr ⟨d, hf⟩

end FP

end Complexity

namespace Complexity.TimeSpaceModel

variable {Data α β : Type*} [UniqueEncoding Data α] [Encoding Data β]
  {model : TimeSpaceModel Id Data} {f : α → β} {T S : ℕ → ℕ}

/-- With unique input encodings, a value budget obtained from that encoding's size
is exactly the corresponding actual-code-size budget. -/
theorem ComputableWithin.iff_sizeBudgets :
    model.ComputableWithin f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a))) ↔
    model.ComputableWithSizeBudgets f T S := by
  constructor <;> rintro ⟨R, hR, h⟩ <;> refine ⟨R, hR, ?_⟩
  all_goals
    intro a src ha
    obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
    exact h a _ (by simp)

/-- A size-indexed specialization of an all-input certificate reaches the complexity boundary. -/
theorem ComputableWithin.mem_ftisp
    (h : model.ComputableWithin f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a)))) : f ∈ FTISP model T S :=
  (ComputableWithin.iff_sizeBudgets.mp h).mem_ftisp

/-- Export the same machine; an eventual class conclusion is never used as a call specification. -/
theorem ComputableWithGrowth.mem_ftisp
    (h : model.ComputableWithGrowth f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a)))) : f ∈ FTISP model T S := by
  obtain ⟨t, s, h, ⟨C, ht⟩, ⟨D, hs⟩⟩ := h
  exact FTISP.mono ((Dominated.refl T).const_mul_left C).atTop
    ((Dominated.refl S).const_mul_left D).atTop (h.mono ht hs).mem_ftisp

end Complexity.TimeSpaceModel
