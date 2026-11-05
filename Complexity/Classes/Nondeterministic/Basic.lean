/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Asymptotics.Polynomial

/-!
# Nondeterministic complexity classes

Every valid input is decided by one behavior of the chosen model. Resource bounds
apply to every branch, and every branch terminates with Boolean output. Acceptance
is existential. Simultaneous bounds must use the same behavior.

The asymptotic comparison may ignore finitely many input lengths; correctness,
termination, and the witnessing pointwise bounds hold on every valid code.
-/

@[expose] public section

namespace Complexity

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]

/-- Predicates decidable nondeterministically in time `O(T(n))`. The other resource
still has one bound for each input length. -/
def NTIME (model : TimeSpaceModel Multiset Data) (T : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t, (∃ s, model.NDecidableWithinBySize p t s) ∧
    DominatedAtTop t T}

/-- Predicates decidable nondeterministically in space `O(S(n))`, with
all branches terminating on every valid input. -/
def NSPACE (model : TimeSpaceModel Multiset Data) (S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ s, (∃ t, model.NDecidableWithinBySize p t s) ∧
    DominatedAtTop s S}

/-- Predicates decidable by one nondeterministic behavior satisfying both
asymptotic bounds on every branch. -/
def NTISP (model : TimeSpaceModel Multiset Data) (T S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t s, model.NDecidableWithinBySize p t s ∧
    DominatedAtTop t T ∧ DominatedAtTop s S}

variable {model : TimeSpaceModel Multiset Data} {p q : α → Prop} {T S T' S' : ℕ → ℕ}

namespace NTIME

theorem mono (h : DominatedAtTop T T') : NTIME (α := α) model T ⊆ NTIME model T' := by
  rintro p ⟨t, hp, ht⟩
  exact ⟨t, hp, ht.trans h⟩

theorem congr (h : p ∈ NTIME model T) (hp : ∀ a, p a ↔ q a) : q ∈ NTIME model T :=
  funext (fun a => propext (hp a)) ▸ h

end NTIME

namespace NSPACE

theorem mono (h : DominatedAtTop S S') : NSPACE (α := α) model S ⊆ NSPACE model S' := by
  rintro p ⟨s, hp, hs⟩
  exact ⟨s, hp, hs.trans h⟩

theorem congr (h : p ∈ NSPACE model S) (hp : ∀ a, p a ↔ q a) : q ∈ NSPACE model S :=
  funext (fun a => propext (hp a)) ▸ h

end NSPACE

namespace NTISP

theorem mono (ht : DominatedAtTop T T') (hs : DominatedAtTop S S') :
    NTISP (α := α) model T S ⊆ NTISP model T' S' := by
  rintro p ⟨t, s, h, ht', hs'⟩
  exact ⟨t, s, h, ht'.trans ht, hs'.trans hs⟩

theorem congr (h : p ∈ NTISP model T S) (hp : ∀ a, p a ↔ q a) : q ∈ NTISP model T S :=
  funext (fun a => propext (hp a)) ▸ h

theorem subset_time : NTISP (α := α) model T S ⊆ NTIME model T := by
  rintro p ⟨t, s, h, ht, _⟩
  exact ⟨t, ⟨s, h⟩, ht⟩

theorem subset_space : NTISP (α := α) model T S ⊆ NSPACE model S := by
  rintro p ⟨t, s, h, _, hs⟩
  exact ⟨s, ⟨t, h⟩, hs⟩

theorem subset_inter : NTISP (α := α) model T S ⊆ NTIME model T ∩ NSPACE model S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end NTISP

/-- Predicates decidable by a nondeterministic behavior in polynomial time. -/
def NP (model : TimeSpaceModel Multiset Data) : Set (α → Prop) :=
  ⋃ d : ℕ, NTIME model (fun n => n ^ d)

namespace NP

theorem mem_iff_exists_ntime : p ∈ NP model ↔ ∃ d : ℕ, p ∈ NTIME model (fun n => n ^ d) :=
  Set.mem_iUnion

/-- A pointwise comparison with a polynomial preserves nondeterministic polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : p ∈ NTIME model t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : p ∈ NP model :=
  mem_iff_exists_ntime.mpr ⟨d, NTIME.mono (DominatedAtTop.of_le_mul_add_one_pow c d ht) h⟩

theorem ntime_subset (d : ℕ) : NTIME (α := α) model (fun n => n ^ d) ⊆ NP model :=
  fun _ h => mem_iff_exists_ntime.mpr ⟨d, h⟩

theorem congr (h : p ∈ NP model) (hp : ∀ a, p a ↔ q a) : q ∈ NP model :=
  funext (fun a => propext (hp a)) ▸ h

end NP

end Complexity

namespace Complexity.TimeSpaceModel

section BySize

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
  {model : TimeSpaceModel Multiset Data} {p q : α → Prop} {t s t' s' T S : ℕ → ℕ}

/-- Export the same complete branch computation with both asymptotic bounds. -/
theorem NDecidableWithinBySize.mem_ntisp_of_dominated
    (h : model.NDecidableWithinBySize p t s)
    (ht : DominatedAtTop t T) (hs : DominatedAtTop s S) : p ∈ NTISP model T S :=
  ⟨t, s, h, ht, hs⟩

theorem NDecidableWithinBySize.mem_ntime_of_dominated
    (h : model.NDecidableWithinBySize p t s) (ht : DominatedAtTop t T) :
    p ∈ NTIME model T :=
  ⟨t, ⟨s, h⟩, ht⟩

theorem NDecidableWithinBySize.mem_nspace_of_dominated
    (h : model.NDecidableWithinBySize p t s) (hs : DominatedAtTop s S) :
    p ∈ NSPACE model S :=
  ⟨s, ⟨t, h⟩, hs⟩

theorem NDecidableWithinBySize.mem_ntisp
    (h : model.NDecidableWithinBySize p t s) : p ∈ NTISP model t s :=
  h.mem_ntisp_of_dominated (DominatedAtTop.refl _) (DominatedAtTop.refl _)

theorem NDecidableWithinBySize.mem_ntime
    (h : model.NDecidableWithinBySize p t s) : p ∈ NTIME model t :=
  h.mem_ntime_of_dominated (DominatedAtTop.refl _)

theorem NDecidableWithinBySize.mem_nspace
    (h : model.NDecidableWithinBySize p t s) : p ∈ NSPACE model s :=
  h.mem_nspace_of_dominated (DominatedAtTop.refl _)

end BySize

variable {Data α : Type*} [UniqueEncoding Data α] [Encoding Data Bool]
  {model : TimeSpaceModel Multiset Data} {p : α → Prop} {T S : ℕ → ℕ}

/-- Export one all-branch certificate specialized to encoding size. -/
theorem NDecidableWithin.mem_ntisp
    (h : model.NDecidableWithin p
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a)))) : p ∈ NTISP model T S :=
  (NDecidableWithin.iff_bySize.mp h).mem_ntisp

/-- The same behavior supplies both eventual bounds and still covers every legal input. -/
theorem NDecidableIn.mem_ntisp
    (h : model.NDecidableIn p
      IsO(fun a => T (model.inputSize (encode Data a)))
      IsO(fun a => S (model.inputSize (encode Data a)))) : p ∈ NTISP model T S := by
  obtain ⟨t, s, h, ⟨C, ht⟩, ⟨D, hs⟩⟩ := h
  exact NTISP.mono ((Dominated.refl T).const_mul_left C).atTop
    ((Dominated.refl S).const_mul_left D).atTop (h.mono ht hs).mem_ntisp

end Complexity.TimeSpaceModel
