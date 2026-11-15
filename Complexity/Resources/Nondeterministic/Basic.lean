/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Encoding.RawWord
public import Complexity.Models.TuringMachine.Nondeterministic.Basic

/-!
# Resource bounds for nondeterministic decisions

A single binary-choice machine handles every valid input code. The behaviours of the model are
`TM.ComputesWithinWith` on `Multiset`: every history of every branch obeys both budgets, and at some
step every branch has halted; the outputs of all branches at that step, with their multiplicities,
are the outputs of the behaviour. A decision asks every output to be the code of a Boolean, and a
predicate holds exactly when some branch outputs `true`. On the machine, `NTM.DecidesWithin` is the
Boolean special case: `ComputesWithinWith` to the codes of a multiset of Booleans `bs`, with
`true ∈ bs` exactly when the predicate holds. Time and work-space bounds apply to every branch, not
merely to an accepting witness. The space-only specification still requires termination.

Raw bit strings occupy `some b` input cells, and `none` is blank. Resource budgets depend
on the decoded value and uniformly cover every representation of that value.
Invalid codes impose no obligations.
-/

@[expose] public section

namespace Complexity.NTM

/-- Finite binary-choice Turing machines, retaining all branch outputs and their
multiplicities. Resource bounds cover every branch, including rejecting branches. The outputs are
read at any step by which every branch has halted. -/
def _root_.Complexity.TimeSpaceModel.ntm : TimeSpaceModel Multiset (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : NTM κ (Option Bool) Q), R = fun (xs : RawWord Bool) ys =>
        M.ComputesWithinWith Multiset (xs.toList.map some) (ys.map fun y ↦ y.toList.map some)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

section InputBudgets

variable {α : Type*} [Encoding (RawWord Bool) α]
  {κ Q : Type} {M : NTM κ (Option Bool) Q} {p : α → Prop} {t s : α → ℕ}

/-- On every legal input code, `M` computes the codes of a multiset of Booleans within the
value-indexed budgets, and `true` is among them exactly when `p` holds. -/
def DecidesWithin [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop) (t s : α → ℕ) : Prop :=
  ∀ (r : RawWord Bool) a, a ∈ decode α r → ∃ bs : Multiset Bool,
    M.ComputesWithinWith Multiset (r.toList.map some) (bs.map fun b ↦ ⌜b⌝₂.toList.map some)
      (t a) (s a) ∧ (true ∈ bs ↔ p a)

theorem DecidesWithin.mono [Fintype κ]
    (h : DecidesWithin M p t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    DecidesWithin M p t' s' :=
  fun r a ha ↦ (h r a ha).imp fun _ ↦ .imp_left (·.mono (ht a) (hs a))

theorem nDecidableWithin_iff :
    TimeSpaceModel.ntm.NDecidableWithin p t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesWithin M p t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    refine ⟨κ, hκ, Q, hQ, M, fun r a ha ↦ ?_⟩
    obtain ⟨bs, hc, hp⟩ := Encoding.NDecides.iff_of_uniqueOutput.1 h a r ha
    exact ⟨bs, by rwa [Multiset.map_map] at hc, hp⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    refine ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, Encoding.NDecides.iff_of_uniqueOutput.2 fun a r ha ↦ ?_⟩
    obtain ⟨bs, hc, hp⟩ := h r a ha
    exact ⟨bs, by rwa [Multiset.map_map], hp⟩

theorem DecidesWithin.nDecidableWithin [Fintype κ] [Finite Q] (h : DecidesWithin M p t s) :
    TimeSpaceModel.ntm.NDecidableWithin p t s :=
  nDecidableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.NTM
