/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice
public import Complexity.Models.TuringMachine.Basic

/-!
# Binary nondeterministic Turing machines

`NTM` specializes the existing tape model to two labelled alternatives. Finite runs and
traces use the default `Multiset` interpretation, retaining distinct computation paths.
Time bounds cover every branch. Space is measured separately on every finite trace,
including nonhalting traces, rather than on the union of different branches' visits.

`Terminates` requires a finite deadline for all branches on this input. No uniform bound
across input lengths is part of that property. Decision outputs are exactly one Boolean,
and acceptance means that some finite branch halts with `true`.
-/

@[expose] public section

namespace Complexity

/-- A Turing machine with exactly two labelled choices at every active step. -/
abbrev NTM (κ : Type*) (Γ Q : Type*) := TM BinaryChoice κ Γ Q

namespace NTM

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
  ∀ n cs, cs ∈ M.runTraceWith Multiset
      (M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs) n →
    TM.spaceUsedOfTrace cs ≤ s

theorem UsesTime.mono {M : NTM κ Γ Q} {xs : List Γ} {t t' : ℕ}
    (h : M.UsesTime xs t) (ht : t ≤ t') : M.UsesTime xs t' :=
  Controller.forall_halted_runFromWith_mono M
    (M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs) h ht

theorem UsesTime.terminates {M : NTM κ Γ Q} {xs : List Γ} {t : ℕ}
    (h : M.UsesTime xs t) : M.Terminates xs := ⟨t, h⟩

theorem UsesSpace.mono [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s s' : ℕ}
    (h : M.UsesSpace xs s) (hs : s ≤ s') : M.UsesSpace xs s' :=
  fun n cs hc => (h n cs hc).trans hs

/-- Initial head positions count toward space, even at time zero. -/
theorem UsesSpace.tapes_le [Fintype κ] {M : NTM κ Γ Q} {xs : List Γ} {s : ℕ}
    (h : M.UsesSpace xs s) : Fintype.card κ ≤ s := by
  have hh := h 0 [M.initInput (Config := TM.Cfg κ Γ Q xs.toArray) xs]
    (Multiset.mem_singleton_self _)
  simpa [TM.spaceUsedOfTrace, TM.visitedOfTrace] using hh

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

section Boolean

variable {M : NTM κ (Option Bool) Q} {xs : List (Option Bool)}

/-- Every halted branch returns exactly one Boolean bit, including rejecting branches. -/
def BooleanOutput (M : NTM κ (Option Bool) Q) (xs : List (Option Bool)) : Prop :=
  ∀ ys, M.Produces xs ys → ∃ b : Bool, ys = [some b]

/-- An input is accepted when some finite branch halts with the single bit `true`. -/
def Accepts (M : NTM κ (Option Bool) Q) (xs : List (Option Bool)) : Prop :=
  M.Produces xs [some true]

theorem accepts_iff_of_usesTime {t : ℕ} (h : M.UsesTime xs t) :
    M.Accepts xs ↔ ∃ c ∈ M.runWith
      (TM.Cfg κ (Option Bool) Q xs.toArray) Multiset xs t,
        c.output = #[some true] :=
  produces_iff_of_usesTime h

theorem booleanOutput_iff_of_usesTime {t : ℕ} (h : M.UsesTime xs t) :
    M.BooleanOutput xs ↔ ∀ c ∈ M.runWith
      (TM.Cfg κ (Option Bool) Q xs.toArray) Multiset xs t,
        ∃ b : Bool, c.output = #[some b] := by
  constructor
  · intro hb c hc
    obtain ⟨b, hb⟩ := hb c.output.toList
      ((produces_iff_of_usesTime h).2 ⟨c, hc, by simp⟩)
    exact ⟨b, by simpa using congrArg List.toArray hb⟩
  · intro hb ys hy
    obtain ⟨c, hc, hy⟩ := (produces_iff_of_usesTime h).1 hy
    obtain ⟨b, hb⟩ := hb c hc
    exact ⟨b, by simpa using congrArg Array.toList (hy.symm.trans hb)⟩

end Boolean
end NTM
end Complexity
