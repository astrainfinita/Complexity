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

/-- Predicates decidable nondeterministically in time `O(T(n))`. -/
def NTIME (model : TimeSpaceModel Multiset Data) (T : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t, model.NDecidableInTime p t ∧ IsBigO t T}

/-- Predicates decidable nondeterministically in space `O(S(n))`, with
all branches terminating on every valid input. -/
def NSPACE (model : TimeSpaceModel Multiset Data) (S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ s, model.NDecidableInSpace p s ∧ IsBigO s S}

/-- Predicates decidable by one nondeterministic behavior satisfying both
asymptotic bounds on every branch. -/
def NTISP (model : TimeSpaceModel Multiset Data) (T S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t s, model.NDecidableInTimeAndSpace p t s ∧ IsBigO t T ∧ IsBigO s S}

variable {model : TimeSpaceModel Multiset Data} {p q : α → Prop} {T S T' S' : ℕ → ℕ}

theorem TimeSpaceModel.NDecidableInTime.mem_ntime
    (h : model.NDecidableInTime p T) : p ∈ NTIME model T :=
  ⟨T, h, IsBigO.refl T⟩

theorem TimeSpaceModel.NDecidableInSpace.mem_nspace
    (h : model.NDecidableInSpace p S) : p ∈ NSPACE model S :=
  ⟨S, h, IsBigO.refl S⟩

theorem TimeSpaceModel.NDecidableInTimeAndSpace.mem_ntisp
    (h : model.NDecidableInTimeAndSpace p T S) : p ∈ NTISP model T S :=
  ⟨T, S, h, IsBigO.refl T, IsBigO.refl S⟩

namespace NTIME

theorem mono (h : IsBigO T T') : NTIME (α := α) model T ⊆ NTIME model T' := by
  rintro p ⟨t, hp, ht⟩
  exact ⟨t, hp, ht.trans h⟩

theorem congr (h : p ∈ NTIME model T) (hp : ∀ a, p a ↔ q a) : q ∈ NTIME model T :=
  funext (fun a => propext (hp a)) ▸ h

end NTIME

namespace NSPACE

theorem mono (h : IsBigO S S') : NSPACE (α := α) model S ⊆ NSPACE model S' := by
  rintro p ⟨s, hp, hs⟩
  exact ⟨s, hp, hs.trans h⟩

theorem congr (h : p ∈ NSPACE model S) (hp : ∀ a, p a ↔ q a) : q ∈ NSPACE model S :=
  funext (fun a => propext (hp a)) ▸ h

end NSPACE

namespace NTISP

theorem mono (ht : IsBigO T T') (hs : IsBigO S S') :
    NTISP (α := α) model T S ⊆ NTISP model T' S' := by
  rintro p ⟨t, s, h, ht', hs'⟩
  exact ⟨t, s, h, ht'.trans ht, hs'.trans hs⟩

theorem congr (h : p ∈ NTISP model T S) (hp : ∀ a, p a ↔ q a) : q ∈ NTISP model T S :=
  funext (fun a => propext (hp a)) ▸ h

theorem subset_time : NTISP (α := α) model T S ⊆ NTIME model T := by
  rintro p ⟨t, s, h, ht, _⟩
  exact ⟨t, h.nDecidableInTime, ht⟩

theorem subset_space : NTISP (α := α) model T S ⊆ NSPACE model S := by
  rintro p ⟨t, s, h, _, hs⟩
  exact ⟨s, h.nDecidableInSpace, hs⟩

theorem subset_inter : NTISP (α := α) model T S ⊆ NTIME model T ∩ NSPACE model S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end NTISP

/-- Predicates decidable by a nondeterministic behavior in polynomial time. -/
def NP (model : TimeSpaceModel Multiset Data) : Set (α → Prop) :=
  ⋃ d : ℕ, NTIME model (fun n => n ^ d)

namespace NP

theorem mem_iff_exists_ntime : p ∈ NP model ↔ ∃ d : ℕ, p ∈ NTIME model (fun n => n ^ d) :=
  Set.mem_iUnion

/-- A pointwise bound by `c * (n + 1) ^ d` establishes polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : model.NDecidableInTime p t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : p ∈ NP model :=
  mem_iff_exists_ntime.mpr ⟨d, t, h, IsBigO.of_le_mul_add_one_pow c d ht⟩

theorem ntime_subset (d : ℕ) : NTIME (α := α) model (fun n => n ^ d) ⊆ NP model :=
  fun _ h => mem_iff_exists_ntime.mpr ⟨d, h⟩

theorem congr (h : p ∈ NP model) (hp : ∀ a, p a ↔ q a) : q ∈ NP model :=
  funext (fun a => propext (hp a)) ▸ h

end NP

end Complexity
