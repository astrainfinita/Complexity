/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice.Basic
public import Complexity.Control.Controller.RunHistory
public import Complexity.Models.TuringMachine.Cost

/-!
# Binary nondeterministic Turing machines

`NTM` specializes the existing tape model to two labelled alternatives. Finite runs use
the default `Multiset` interpretation, retaining the multiplicity of computation paths.

Time and space are stated with the general facilities for runs, not with definitions of this
model. Both are read from the histories that a run can return at any depth,
`M.histories Multiset xs`, which include every finite prefix of a nonhalting branch. A time bound
`t` and a space bound `s` together are
`∀ h ∈ M.histories Multiset xs, h.length ≤ t ∧ h.snd.space ≤ s`. Termination is a common finite
bound for all branches on this input, `∃ t, ∀ h ∈ M.histories Multiset xs, h.length ≤ t`. None of
these is uniform across input lengths. `Controller.forall_halted_succ_of_forall_length_le` gives
a step at which every branch has halted, `Controller.length_le_of_forall_halted` goes back, and
`Controller.forall_mem_histories` proves a step invariant. Each history bounds its space by its
length, `History.space_le_length`, so a time bound also bounds space.

Output interpretations belong to the resource interface; the machine itself produces lists of
symbols.
-/

@[expose] public section

namespace Complexity

/-- A Turing machine with exactly two labelled choices at every active step. -/
abbrev NTM (κ : Type*) (Γ Q : Type*) := TM BinaryChoice κ Γ Q

namespace NTM

open Controller (History)

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : List Γ}

/-- Initial head positions count toward space, even at time zero. -/
theorem card_le_of_forall_space_le [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s : ℕ}
    (hs : ∀ h ∈ M.histories Multiset xs, h.snd.space ≤ s) : Fintype.card κ ≤ s := by
  simpa only [History.snd_nil, History.space_nil] using
    hs _ ((M.mem_histories_iff Multiset xs).2 ⟨0, Multiset.mem_singleton_self _⟩)

/-- Some finite computation halts with the given complete output. -/
def Produces (M : NTM κ Γ Q) (xs ys : List Γ) : Prop :=
  ∃ n c, c ∈ M.runWith Multiset xs n ∧ M.Halted c ∧ c.2.output = ys.toArray

/-- A common halting deadline allows eventual output to be checked at one fixed depth. -/
theorem produces_iff_of_forall_halted {M : NTM κ Γ Q} {xs ys : List Γ} {t : ℕ}
    (h : ∀ c ∈ M.runWith Multiset xs t, M.Halted c) :
    M.Produces xs ys ↔ ∃ c ∈ M.runWith Multiset xs t, c.2.output = ys.toArray := by
  constructor
  · rintro ⟨n, c, hc, hh, ho⟩
    refine ⟨c, ?_, ho⟩
    rcases le_total n t with ht | ht
    · exact Controller.mem_runFromWith_of_halted Multiset M
        (M.init xs) hc hh ht
    · rwa [M.runWith_eq_of_forall_halted Multiset xs h ht] at hc
  · rintro ⟨c, hc, ho⟩
    exact ⟨t, c, hc, h c hc, ho⟩

end NTM
end Complexity
