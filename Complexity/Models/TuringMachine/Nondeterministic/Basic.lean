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
  ∀ c ∈ M.runWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs t, M.Halted c

/-- All computation branches halt, with a common finite deadline for this input. -/
def Terminates (M : NTM κ Γ Q) (xs : List Γ) : Prop :=
  ∃ t, M.UsesTime xs t

/-- Every finite computation prefix stays within the work-space bound.
This property alone does not require termination. -/
def UsesSpace [Fintype κ] (M : NTM κ Γ Q) (xs : List Γ) (s : ℕ) : Prop :=
  ∀ n h, h ∈ M.runHistoryWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs n → h.space ≤ s

/-- A step invariant bounds space on every finite computation prefix. -/
theorem usesSpace_of_invariant [Fintype κ] (M : NTM κ Γ Q) {xs : List Γ} {s : ℕ}
    {P : History (TM.Cfg κ Γ Q xs.toArray) (TM.Action κ Γ Q) → Prop}
    (hinit : P (History.nil (M.initInput xs)))
    (hstep : ∀ c, P c → ∀ d ∈ M.stepWith Multiset c, P d)
    (hspace : ∀ c, P c → c.space ≤ s) : M.UsesSpace xs s := by
  intro n h hh
  change h ∈ M.runHistoryFromWith Multiset (M.initInput xs) n at hh
  rw [← M.runFromWith_nil Multiset] at hh
  exact hspace h (Transition.forall_mem_runN (M.stepWith Multiset) hstep hinit n h hh)

theorem UsesTime.mono {M : NTM κ Γ Q} {xs : List Γ} {t t' : ℕ}
    (h : M.UsesTime xs t) (ht : t ≤ t') : M.UsesTime xs t' :=
  Controller.forall_halted_runFromWith_mono M
    (M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs) h ht

theorem UsesTime.terminates {M : NTM κ Γ Q} {xs : List Γ} {t : ℕ}
    (h : M.UsesTime xs t) : M.Terminates xs := ⟨t, h⟩

theorem UsesSpace.mono [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s s' : ℕ}
    (h : M.UsesSpace xs s) (hs : s ≤ s') : M.UsesSpace xs s' :=
  fun n c hc => (h n c hc).trans hs

/-- A time bound also bounds visited work cells on every finite computation prefix. -/
theorem UsesTime.usesSpace [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {t : ℕ}
    (ht : M.UsesTime xs t) : M.UsesSpace xs (Fintype.card κ * (t + 1)) := by
  let c : TM.Cfg κ Γ Q xs.toArray := M.initInput xs
  intro n h hh
  apply h.space_le_length.trans
  apply Nat.mul_le_mul_left
  apply Nat.succ_le_succ
  by_cases hn : n ≤ t
  · exact (M.runHistoryFromWith_mem_spec c n hh).length_le.trans hn
  · have hall : ∀ p ∈ M.runFromWith Multiset
        (History.nil (Action := TM.Action κ Γ Q) c) t, M.Halted p := by
      change ∀ d ∈ M.runFromWith Multiset c t, M.Halted d at ht
      rw [← M.last_runHistoryFromWith Multiset c t,
        Multiset.fmap_def, Multiset.forall_mem_map_iff] at ht
      simpa only [M.runFromWith_nil Multiset, Controller.halted_history] using ht
    have he := M.runFromWith_eq_of_forall_halted
      (History.nil (Action := TM.Action κ Γ Q) c) hall (Nat.le_of_not_ge hn)
    simp only [M.runFromWith_nil Multiset] at he
    change h ∈ M.runHistoryFromWith Multiset c n at hh
    rw [he] at hh
    exact (M.runHistoryFromWith_mem_spec c t hh).length_le

/-- Initial head positions count toward space, even at time zero. -/
theorem UsesSpace.tapes_le [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s : ℕ}
    (h : M.UsesSpace xs s) : Fintype.card κ ≤ s := by
  have hh := h 0 _ (Multiset.mem_singleton_self _)
  simpa only [History.space_nil] using hh

/-- Once every branch has halted, additional padding leaves the entire endpoint multiset fixed. -/
theorem runWith_eq_of_usesTime {M : NTM κ Γ Q} {xs : List Γ} {t t' : ℕ}
    (h : M.UsesTime xs t) (ht : t ≤ t') :
    M.runWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs t' =
      M.runWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs t :=
  Controller.runFromWith_eq_of_forall_halted M
    (M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs) h ht

/-- Some finite computation halts with the given complete output. -/
def Produces (M : NTM κ Γ Q) (xs ys : List Γ) : Prop :=
  ∃ n c, c ∈ M.runWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs n ∧
    M.Halted c ∧ c.output = ys.toArray

/-- A time bound allows eventual output to be checked at one fixed depth. -/
theorem produces_iff_of_usesTime {M : NTM κ Γ Q} {xs ys : List Γ} {t : ℕ}
    (h : M.UsesTime xs t) : M.Produces xs ys ↔
      ∃ c ∈ M.runWith (TM.Cfg κ Γ Q xs.toArray) Multiset xs t,
        c.output = ys.toArray := by
  constructor
  · rintro ⟨n, c, hc, hh, ho⟩
    refine ⟨c, ?_, ho⟩
    rcases le_total n t with ht | ht
    · exact Controller.mem_runFromWith_of_halted M
        (M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs) hc hh ht
    · rwa [runWith_eq_of_usesTime h ht] at hc
  · rintro ⟨c, hc, ho⟩
    exact ⟨t, c, hc, h c hc, ho⟩

end NTM
end Complexity
