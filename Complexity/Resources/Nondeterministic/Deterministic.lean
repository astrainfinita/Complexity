/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Models.TuringMachine.Nondeterministic.Deterministic

/-!
# Deterministic decision specifications as nondeterministic specifications

Duplicating the transitions of a Boolean-valued deterministic computation yields
a nondeterministic decider for the same predicate, with identical time and work
space. Both specifications cover every valid input encoding.
-/

@[expose] public section

namespace Complexity.TM

section InputBudgets

variable {α : Type*} [Encoding (RawWord Bool) α]
  {f : α → Bool} {p : α → Prop} {t s : α → ℕ}

private theorem toBinary_decides {κ : Type*} [Fintype κ] {Q : Type*}
    {M : TM Id κ (Option Bool) Q} {src : RawWord Bool} {output : Bool}
    {t s : ℕ}
    (h : M.ComputesWithin (src.toList.map some)
      ((encode (RawWord Bool) output).toList.map some) t s) :
    NTM.UsesTime M.toBinary (src.toList.map some) t ∧
      NTM.UsesSpace M.toBinary (src.toList.map some) s ∧
      NTM.BooleanOutput M.toBinary src ∧
      (NTM.Accepts M.toBinary src ↔ output = true) := by
  obtain ⟨hhalt, hout⟩ := h.run_spec
  have ht := (M.usesTime_toBinary_iff _ _).2 hhalt
  refine ⟨ht, (M.usesSpace_toBinary_iff _ _).2 h.usesSpace, ?_, ?_⟩
  · rw [NTM.booleanOutput_iff_of_usesTime ht]
    intro c hc
    obtain rfl := (M.mem_runWith_toBinary_iff _ _ _).1 hc
    exact ⟨output, hout⟩
  · rw [NTM.accepts_iff_of_usesTime ht]
    simp only [Controller.mem_runWith_toBinary_iff, exists_eq_left, hout, Array.mk.injEq,
      List.map_inj_right (fun _ _ => Option.some.inj), RawWord.toList_inj,
      UniqueEncoding.encode_inj]

/-- Duplicating deterministic transitions preserves both input-dependent budgets on all
branches, rather than only an accepting execution. -/
theorem Computes.decidesWithin {κ : Type*} [Fintype κ] {Q : Type*}
    {M : TM Id κ (Option Bool) Q} (h : Computes M f t s) (hp : Decides f p) :
    NTM.DecidesWithin M.toBinary p t s := by
  have h := Encoding.Computes.iff_of_uniqueOutput.mp h
  intro src a hsrc
  obtain ⟨ht, hs, hvalid, haccept⟩ := toBinary_decides (h a src hsrc)
  exact ⟨ht, hs, hvalid, haccept.trans (hp a)⟩

/-- Duplicating a deterministic machine preserves the budgets for the actual input
code, and retains every halted branch in the nondeterministic output multiset. -/
theorem nDecidableWithinByCode_of_computable {t s : α → RawWord Bool → ℕ}
    (h : TimeSpaceModel.tm.ComputableWithinByCode f t s) (hp : Decides f p) :
    TimeSpaceModel.ntm.NDecidableWithinByCode p t s := by
  obtain ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩ := h
  refine ⟨_, ⟨κ, hκ, Q, hQ, M.toBinary, rfl⟩, fun a r ha => ?_⟩
  obtain ⟨q, hq, hc⟩ := h a r ha
  obtain rfl := UniqueEncoding.mem_decode_iff.mp hq
  simp only [Id.run_pure] at hc
  obtain ⟨ht, hs, hvalid, haccept⟩ := toBinary_decides hc
  simp only [and_assoc, exists_and_left]
  refine ⟨ht, hs, (NTM.exists_boolean_outputs_iff _ _ _).mpr ?_⟩
  exact ⟨(NTM.booleanOutput_iff_of_usesTime ht).mp hvalid,
    (NTM.accepts_iff_of_usesTime ht).symm.trans (haccept.trans (hp a))⟩

theorem nDecidableWithin_of_computable
    (h : TimeSpaceModel.tm.ComputableWithin f t s) (hp : Decides f p) :
    TimeSpaceModel.ntm.NDecidableWithin p t s :=
  nDecidableWithinByCode_of_computable h hp

theorem nDecidableIn_of_computable {time space : (α → ℕ) → Prop}
    (h : TimeSpaceModel.tm.ComputableIn f time space) (hp : Decides f p) :
    TimeSpaceModel.ntm.NDecidableIn p time space := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨u, v, nDecidableWithin_of_computable h hp, hu, hv⟩

end InputBudgets

end Complexity.TM
