/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic
public import Complexity.Asymptotics.Polynomial

/-!
# Nondeterministic complexity classes

Every valid input is decided by one fixed finite binary-choice machine. Resource
bounds apply to every branch, and every branch terminates with Boolean output.
Acceptance is existential. Simultaneous bounds must use the same machine.

The asymptotic comparison may ignore finitely many input lengths; correctness,
termination, and the witnessing pointwise bounds hold on every valid code.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable nondeterministically in time `O(T(n))`. -/
def NTIME (T : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t, NTM.DecidableInTime p t ∧ IsBigO t T}

/-- Predicates decidable nondeterministically in work space `O(S(n))`, with
all branches terminating on every valid input. -/
def NSPACE (S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ s, NTM.DecidableInSpace p s ∧ IsBigO s S}

/-- Predicates decidable by one nondeterministic machine satisfying both
asymptotic bounds on every branch. -/
def NTISP (T S : ℕ → ℕ) : Set (α → Prop) :=
  {p | ∃ t s, NTM.DecidableInTimeAndSpace p t s ∧ IsBigO t T ∧ IsBigO s S}

variable {p q : α → Prop} {T S T' S' : ℕ → ℕ}

namespace NTIME

theorem of_decidableInTime (h : NTM.DecidableInTime p T) : p ∈ NTIME T :=
  ⟨T, h, IsBigO.refl T⟩

theorem mono (h : IsBigO T T') : NTIME (α := α) T ⊆ NTIME T' := by
  rintro p ⟨t, hp, ht⟩
  exact ⟨t, hp, ht.trans h⟩

theorem congr (h : p ∈ NTIME T) (hp : ∀ a, p a ↔ q a) : q ∈ NTIME T := by
  obtain ⟨t, h, ht⟩ := h
  exact ⟨t, h.congr hp, ht⟩

end NTIME

namespace NSPACE

theorem of_decidableInSpace (h : NTM.DecidableInSpace p S) : p ∈ NSPACE S :=
  ⟨S, h, IsBigO.refl S⟩

theorem mono (h : IsBigO S S') : NSPACE (α := α) S ⊆ NSPACE S' := by
  rintro p ⟨s, hp, hs⟩
  exact ⟨s, hp, hs.trans h⟩

theorem congr (h : p ∈ NSPACE S) (hp : ∀ a, p a ↔ q a) : q ∈ NSPACE S := by
  obtain ⟨s, h, hs⟩ := h
  exact ⟨s, h.congr hp, hs⟩

end NSPACE

namespace NTISP

theorem of_decidableInTimeAndSpace (h : NTM.DecidableInTimeAndSpace p T S) :
    p ∈ NTISP T S := ⟨T, S, h, IsBigO.refl T, IsBigO.refl S⟩

theorem mono (ht : IsBigO T T') (hs : IsBigO S S') :
    NTISP (α := α) T S ⊆ NTISP T' S' := by
  rintro p ⟨t, s, h, ht', hs'⟩
  exact ⟨t, s, h, ht'.trans ht, hs'.trans hs⟩

theorem congr (h : p ∈ NTISP T S) (hp : ∀ a, p a ↔ q a) : q ∈ NTISP T S := by
  obtain ⟨t, s, h, ht, hs⟩ := h
  exact ⟨t, s, h.congr hp, ht, hs⟩

theorem subset_time : NTISP (α := α) T S ⊆ NTIME T := by
  rintro p ⟨t, s, h, ht, _⟩
  exact ⟨t, h.decidableInTime, ht⟩

theorem subset_space : NTISP (α := α) T S ⊆ NSPACE S := by
  rintro p ⟨t, s, h, _, hs⟩
  exact ⟨s, h.decidableInSpace, hs⟩

theorem subset_inter : NTISP (α := α) T S ⊆ NTIME T ∩ NSPACE S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end NTISP

/-- Predicates decidable by a finite nondeterministic machine in polynomial time. -/
def NP : Set (α → Prop) :=
  ⋃ d : ℕ, NTIME (fun n => n ^ d)

namespace NP

theorem mem_iff_exists_ntime : p ∈ NP ↔ ∃ d : ℕ, p ∈ NTIME (fun n => n ^ d) :=
  Set.mem_iUnion

/-- A pointwise bound by `c * (n + 1) ^ d` establishes polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : NTM.DecidableInTime p t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : p ∈ NP :=
  mem_iff_exists_ntime.mpr ⟨d, t, h, IsBigO.of_le_mul_add_one_pow c d ht⟩

theorem ntime_subset (d : ℕ) : NTIME (α := α) (fun n => n ^ d) ⊆ NP :=
  fun _ h => mem_iff_exists_ntime.mpr ⟨d, h⟩

theorem congr (h : p ∈ NP) (hp : ∀ a, p a ↔ q a) : q ∈ NP := by
  obtain ⟨d, h⟩ := mem_iff_exists_ntime.mp h
  exact mem_iff_exists_ntime.mpr ⟨d, NTIME.congr h hp⟩

end NP

end Complexity
