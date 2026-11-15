/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Control.Controller.Binary

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

private theorem toBinary_decides {κ Q : Type} [Fintype κ] {M : TM Id κ (Option Bool) Q}
    {src : RawWord Bool} {output : Bool} {t s : ℕ}
    (h : M.ComputesWithin (src.toList.map some) (⌜output⌝₂.toList.map some) t s) :
    ∃ bs : Multiset Bool, ComputesWithinWith Multiset M.toBinary (src.toList.map some)
      (bs.map fun b ↦ ⌜b⌝₂.toList.map some) t s ∧ (true ∈ bs ↔ output = true) := by
  obtain ⟨hhalt, hout⟩ := h.run_spec
  refine ⟨(M.toBinary.runWith Multiset (src.toList.map some) t).map fun _ ↦ output,
    ⟨(M.forall_mem_histories_toBinary_iff (src.toList.map some)).2 fun n ↦
      ⟨(Controller.History.length_snd _).trans_le (M.length_runHistory_le_of_halted _ hhalt n),
        h.space_le n⟩, ?_⟩, ?_⟩
  · rw [Multiset.map_map]
    exact M.computesWith_toBinary hhalt hout
  · simp only [Multiset.mem_map, Controller.mem_runWith_toBinary_iff, exists_eq_left]

/-- Duplicating deterministic transitions preserves both input-dependent budgets on all
branches, rather than only an accepting execution. -/
theorem Computes.decidesWithin {κ Q : Type} [Fintype κ] {M : TM Id κ (Option Bool) Q}
    (h : Computes M f t s) (hp : Decides f p) : NTM.DecidesWithin M.toBinary p t s := by
  have h := Encoding.Computes.iff_of_uniqueOutput.mp h
  exact fun src a hsrc ↦ (toBinary_decides (h a src hsrc)).imp fun _ ↦ .imp_right (·.trans (hp a))

/-- Duplicating a deterministic machine preserves the budgets for the actual input
code, and retains every halted branch in the nondeterministic output multiset. -/
theorem nDecidableWithinByCode_of_computable {t s : α → RawWord Bool → ℕ}
    (h : TimeSpaceModel.tm.ComputableWithinByCode f t s) (hp : Decides f p) :
    TimeSpaceModel.ntm.NDecidableWithinByCode p t s := by
  obtain ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩ := h
  refine ⟨_, ⟨κ, hκ, Q, hQ, M.toBinary, rfl⟩,
    Encoding.NDecides.iff_of_uniqueOutput.2 fun a r ha ↦ ?_⟩
  obtain ⟨q, hq, hc⟩ := h a r ha
  obtain rfl := UniqueEncoding.mem_decode_iff.mp hq
  obtain ⟨bs, hc, hb⟩ := toBinary_decides hc
  exact ⟨bs, by rwa [Multiset.map_map], hb.trans (hp a)⟩

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
