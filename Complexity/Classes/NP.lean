/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Nondeterministic
public import Complexity.Asymptotics.Polynomial

/-!
# Nondeterministic polynomial time

`NP` uses binary-choice machines with existential acceptance and a polynomial
time bound on every branch. Inputs use their chosen bit-string encoding; no
decision procedure for the represented predicate is assumed.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable by a finite nondeterministic machine in polynomial time. -/
def NP : Set (α → Prop) :=
  ⋃ d : ℕ, NTIME (fun n => n ^ d)

namespace NP

variable {p q : α → Prop}

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
