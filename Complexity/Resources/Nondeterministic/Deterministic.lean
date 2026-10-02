/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic
public import Complexity.Resources.TuringMachine
public import Complexity.Models.TuringMachine.Nondeterministic.Deterministic
public import Complexity.Encoding.Bool

/-!
# Deterministic decision specifications as nondeterministic specifications

Duplicating the transitions of a Boolean-valued deterministic computation yields
a nondeterministic decider for the same predicate, with identical time and work
space. Both specifications cover every valid input encoding.
-/

@[expose] public section

namespace Complexity.TM

variable {α : Type*} [Encoding (List Bool) α]
variable {f : α → Bool} {p : α → Prop} {t s : ℕ → ℕ}

/-- A deterministic Boolean computation decides the same predicate after
duplicating its transitions, without changing either resource bound. -/
theorem Computes.decidesInTimeAndSpace {κ : Type*} [Fintype κ] {Q : Type*}
    {M : TM Id κ (Option Bool) Q} (h : Computes M f t s) (hp : Decides f p) :
    NTM.DecidesInTimeAndSpace M.toBinary p t s := by
  rw [computes_iff] at h
  have hh : ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
      M.ComputesInTimeAndSpace (xs.map some) [some (f a)]
        (t xs.length) (s xs.length) := by
    simpa using (Computes.iff_of_uniqueOutput.mp h)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro xs a ha
    have hc := hh xs a ha
    obtain ⟨hhalt, hout⟩ := hc.run_spec
    have ht := (M.usesTime_toBinary_iff _ _).2 hhalt
    refine ⟨ht.terminates, ?_, ?_⟩
    · rw [NTM.booleanOutput_iff_of_usesTime ht]
      intro c hc'
      obtain rfl := (M.mem_runWith_toBinary_iff _ _ _).1 hc'
      exact ⟨f a, hout⟩
    · rw [NTM.accepts_iff_of_usesTime ht]
      simpa [hout] using hp a
  · intro xs a ha
    exact (M.usesTime_toBinary_iff _ _).2 (hh xs a ha).run_spec.1
  · intro xs a ha
    exact (M.usesSpace_toBinary_iff _ _).2 (hh xs a ha).usesSpace

theorem decidableInTimeAndSpace_of_computable
    (h : timeSpaceModel.ComputableInTimeAndSpace f t s) (hp : Decides f p) :
    NTM.DecidableInTimeAndSpace p t s := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  exact ⟨κ, hκ, Q, hQ, M.toBinary, h.decidesInTimeAndSpace hp⟩

theorem decidableInTime_of_computable (h : timeSpaceModel.ComputableInTime f t)
    (hp : Decides f p) : NTM.DecidableInTime p t := by
  obtain ⟨s, h⟩ := h
  exact (decidableInTimeAndSpace_of_computable h hp).decidableInTime

theorem decidableInSpace_of_computable (h : timeSpaceModel.ComputableInSpace f s)
    (hp : Decides f p) : NTM.DecidableInSpace p s := by
  obtain ⟨t, h⟩ := h
  exact (decidableInTimeAndSpace_of_computable h hp).decidableInSpace

end Complexity.TM
