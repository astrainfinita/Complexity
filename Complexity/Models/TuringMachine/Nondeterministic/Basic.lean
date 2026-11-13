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
Time bounds cover every branch. Space is read from each branch's execution history
and bounds every finite prefix, including nonhalting branches.

`Terminates` requires a finite deadline for all branches on this input. No uniform bound
across input lengths is part of that property. Output interpretations belong to the
resource interface; the machine itself produces lists of symbols.
-/

@[expose] public section

namespace Complexity

/-- A Turing machine with exactly two labelled choices at every active step. -/
abbrev NTM (κ : Type*) (Γ Q : Type*) := TM BinaryChoice κ Γ Q

namespace NTM

open Controller (History)

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : List Γ}

/-- Every computation branch has halted by this deadline. -/
def UsesTime (M : NTM κ Γ Q) (xs : List Γ) (t : ℕ) : Prop :=
  ∀ c ∈ M.runWith Multiset xs t, M.Halted c

/-- All computation branches halt, with a common finite deadline for this input. -/
def Terminates (M : NTM κ Γ Q) (xs : List Γ) : Prop :=
  ∃ t, M.UsesTime xs t

/-- Every finite computation prefix stays within the work-space bound.
This property alone does not require termination. -/
def UsesSpace [Fintype κ] (M : NTM κ Γ Q) (xs : List Γ) (s : ℕ) : Prop :=
  ∀ n h, h ∈ M.runHistoryWith Multiset xs n → h.snd.space ≤ s

/-- A step invariant bounds space on every finite computation prefix. -/
theorem usesSpace_of_invariant [Fintype κ] (M : NTM κ Γ Q) {xs : List Γ} {s : ℕ}
    {P : History (Q × TM.Cfg κ Γ xs.toArray) (Q × TM.Action κ Γ) → Prop}
    (hinit : P (History.nil (M.init xs)))
    (hstep : ∀ c, P c → ∀ d ∈ M.stepWith Multiset c, P d)
    (hspace : ∀ c, P c → c.snd.space ≤ s) : M.UsesSpace xs s :=
  fun n h hh ↦
    hspace h (M.forall_mem_runFromWith Multiset hstep hinit n h hh)

theorem UsesTime.mono {M : NTM κ Γ Q} {xs : List Γ} {t t' : ℕ}
    (h : M.UsesTime xs t) (ht : t ≤ t') : M.UsesTime xs t' :=
  Controller.forall_halted_runFromWith_mono Multiset M
    (M.init xs) h ht

theorem UsesTime.terminates {M : NTM κ Γ Q} {xs : List Γ} {t : ℕ}
    (h : M.UsesTime xs t) : M.Terminates xs := ⟨t, h⟩

theorem UsesSpace.mono [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s s' : ℕ}
    (h : M.UsesSpace xs s) (hs : s ≤ s') : M.UsesSpace xs s' :=
  fun n c hc => (h n c hc).trans hs

/-- A time bound also bounds visited work cells on every finite computation prefix. -/
theorem UsesTime.usesSpace [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {t : ℕ}
    (ht : M.UsesTime xs t) : M.UsesSpace xs (Fintype.card κ * (t + 1)) := by
  let c : Q × TM.Cfg κ Γ xs.toArray := M.init xs
  intro n h hh
  apply h.snd.space_le_length.trans
  rw [History.length_snd]
  apply Nat.mul_le_mul_left
  apply Nat.succ_le_succ
  by_cases hn : n ≤ t
  · exact (M.runHistoryFromWith_spec Multiset c n h hh).length_le.trans hn
  · rw [UsesTime, Controller.runWith, ← M.last_runHistoryFromWith Multiset, Multiset.fmap_def,
      Multiset.forall_mem_map_iff] at ht
    rw [Controller.runHistoryWith, Controller.runHistoryFromWith,
      M.runFromWith_eq_of_forall_halted Multiset _ ht (Nat.le_of_not_ge hn)] at hh
    exact (M.runHistoryFromWith_spec Multiset c t h hh).length_le

/-- Initial head positions count toward space, even at time zero. -/
theorem UsesSpace.tapes_le [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s : ℕ}
    (h : M.UsesSpace xs s) : Fintype.card κ ≤ s := by
  have hh := h 0 _ (Multiset.mem_singleton_self _)
  simpa only [History.snd_nil, History.space_nil] using hh

/-- Once every branch has halted, additional padding leaves the entire endpoint multiset fixed. -/
theorem runWith_eq_of_usesTime {M : NTM κ Γ Q} {xs : List Γ} {t t' : ℕ}
    (h : M.UsesTime xs t) (ht : t ≤ t') :
    M.runWith Multiset xs t' = M.runWith Multiset xs t :=
  Controller.runFromWith_eq_of_forall_halted Multiset M
    (M.init xs) h ht

/-- Some finite computation halts with the given complete output. -/
def Produces (M : NTM κ Γ Q) (xs ys : List Γ) : Prop :=
  ∃ n c, c ∈ M.runWith Multiset xs n ∧ M.Halted c ∧ c.2.output = ys.toArray

/-- A time bound allows eventual output to be checked at one fixed depth. -/
theorem produces_iff_of_usesTime {M : NTM κ Γ Q} {xs ys : List Γ} {t : ℕ}
    (h : M.UsesTime xs t) : M.Produces xs ys ↔
      ∃ c ∈ M.runWith Multiset xs t,
        c.2.output = ys.toArray := by
  constructor
  · rintro ⟨n, c, hc, hh, ho⟩
    refine ⟨c, ?_, ho⟩
    rcases le_total n t with ht | ht
    · exact Controller.mem_runFromWith_of_halted Multiset M
        (M.init xs) hc hh ht
    · rwa [runWith_eq_of_usesTime h ht] at hc
  · rintro ⟨c, hc, ho⟩
    exact ⟨t, c, hc, h c hc, ho⟩

end NTM
end Complexity
