/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import all Init.Data.List.Scan.Basic
import Complexity.Classes.Nondeterministic.Basic
import Complexity.Resources.Nondeterministic.Basic
import Mathlib.Logic.Equiv.Bool
import Complexity.Models.TuringMachine.Nondeterministic.Deterministic
meta import Complexity.Models.TuringMachine.Nondeterministic.Basic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Cost
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Controller.Basic
meta import Complexity.Control.BinaryChoice.Basic
meta import Complexity.Control.Transition.Basic
meta import Complexity.Data.IntMemory.Basic

open Complexity
open TM (apply)
open Controller (History)

namespace NondeterministicTest

-- A local encoding override does not change the concrete acceptance convention.
example {κ Q : Type*} (M : NTM κ (Option Bool) Q) (xs : RawWord Bool) :
    letI := (inferInstance : UniqueEncoding (RawWord Bool) Bool).ofEquiv Equiv.boolNot
    M.Accepts xs ↔ M.Produces (xs.toList.map some) [some true, some false, some false] := Iff.rfl

private def fixedOutputs (ys : Multiset (RawWord Bool)) : TimeSpaceModel Multiset (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {fun _ zs _ _ => zs = ys}
  budget_mono := by
    rintro R rfl x zs t s t' s' h _ _
    exact h

-- Finite failure rejects; it does not create an accepting branch.
example : (fixedOutputs 0).NDecidableInTimeAndSpace
    (fun _ : List Bool => False) (fun _ => 0) (fun _ => 0) := by
  refine ⟨_, rfl, fun x a ha => ⟨0, rfl, ?_, ?_⟩⟩ <;> simp

example : ¬(fixedOutputs 0).NDecidableInTimeAndSpace
    (fun _ : List Bool => True) (fun _ => 0) (fun _ => 0) := by
  rintro ⟨R, rfl, h⟩
  obtain ⟨ys, rfl, _, h⟩ := h (⌜([] : List Bool)⌝₂) [] (UniqueEncoding.mem_decode_iff.mpr rfl)
  simp at h

-- Even alongside a valid accepting result, a malformed branch invalidates the decision.
example : ¬(fixedOutputs {RawWord.ofList [], ⌜true⌝₂}).NDecidableInTimeAndSpace
    (fun _ : List Bool => True) (fun _ => 0) (fun _ => 0) := by
  rintro ⟨R, rfl, h⟩
  obtain ⟨ys, rfl, hb, _⟩ := h (⌜([] : List Bool)⌝₂) [] (UniqueEncoding.mem_decode_iff.mpr rfl)
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (hb (RawWord.ofList []) (by simp))
  have he := UniqueEncoding.mem_decode_iff.mp hb
  cases b <;> cases he

def answer {Q : Type} (b : Bool) (q : Q) : TM.Action (Fin 0) (Option Bool) Q where
  inputMove := 0
  work := Fin.elim0
  output := some (some b)
  state := q

-- One branch rejects immediately; the other finishes the three-bit code for true.
def guess : NTM (Fin 0) (Option Bool) (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ i :=
    if q = 0 then if i = 0 then answer false 3 else answer true 1
    else answer false (if q = 1 then 2 else 3)

private theorem guess_results (xs : List (Option Bool)) :
    (guess.runWith (TM.Cfg (Fin 0) (Option Bool) (Fin 4) xs.toArray) Multiset xs 3).map
      (fun c => (c.state, c.output)) =
      ↑([(3, #[some false]), (3, #[some true, some false, some false]),
        (3, #[some true, some false, some false]), (3, #[some true, some false, some false]),
        (3, #[some true, some false, some false])] : List (Fin 4 × Array (Option Bool))) := rfl

private theorem guess_time (xs : List (Option Bool)) : guess.UsesTime xs 3 := by
  intro c hc
  have hm := Multiset.mem_map_of_mem (fun c => (c.state, c.output)) hc
  rw [guess_results] at hm
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false, or_self,
    Prod.mk.injEq] at hm
  rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> change (c.state == 3) = true <;> simp [h]

private theorem guess_boolean (xs : RawWord Bool) : guess.BooleanOutput xs := by
  rw [NTM.booleanOutput_iff_of_usesTime (guess_time _)]
  intro c hc
  have hm := Multiset.mem_map_of_mem (fun c => (c.state, c.output)) hc
  rw [guess_results] at hm
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false, or_self,
    Prod.mk.injEq] at hm
  rcases hm with ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

private theorem guess_accepts (xs : RawWord Bool) : guess.Accepts xs := by
  rw [NTM.accepts_iff_of_usesTime (guess_time _)]
  have hm : (3, #[some true, some false, some false]) ∈
      (guess.runWith (TM.Cfg (Fin 0) (Option Bool) (Fin 4) (xs.toList.map some).toArray)
        Multiset (xs.toList.map some) 3).map
        (fun c => (c.state, c.output)) := by rw [guess_results]; simp
  obtain ⟨c, hc, h⟩ := Multiset.mem_map.mp hm
  exact ⟨c, hc, congrArg Prod.snd h⟩

theorem guess_spec : guess.DecidesInTimeAndSpace (fun _ : List Bool => True)
    (fun _ => 3) (fun _ => 0) := by
  intro xs _ _
  refine ⟨guess_time _, ?_, guess_boolean _, iff_true_intro (guess_accepts _)⟩
  intro n c _
  simp [History.space]

example : (fun _ : List Bool => True) ∈ NTISP .ntm (fun _ => 3) (fun _ => 0) :=
  guess_spec.decidableInTimeAndSpace.mem_ntisp

example : (fun _ : List Bool => True) ∈ NP .ntm := by
  apply NP.of_time_le guess_spec.decidesInTime.decidableInTime 3 0
  simp

-- A space-only machine proof supplies its implicit time bound through the model bridge.
example : TimeSpaceModel.ntm.NDecidableInSpace (fun _ : List Bool => True) (fun _ => 0) :=
  guess_spec.decidesInSpace.decidableInSpace

-- The two branches visit [-1,0] and [0,1]: each uses two cells.
def splitHeads : NTM (Fin 1) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ i :=
    { inputMove := 0, work := fun _ => (none, if i = 0 then -1 else 1)
      output := some (some (i == 1)), state := true }

#guard (splitHeads.runHistoryWith (TM.Cfg (Fin 1) (Option Bool) Bool #[])
  Multiset ([] : List (Option Bool)) 1).map (fun h ↦ h.space) = ↑[2, 2]
#guard (splitHeads.runHistoryWith (TM.Cfg (Fin 1) (Option Bool) Bool #[])
  Multiset ([] : List (Option Bool)) 4).map (fun h ↦ h.space) = ↑[2, 2]

-- A local invariant proves the space bound at every depth, including halted padding.
example : splitHeads.UsesSpace [] 2 := by
  apply splitHeads.usesSpace_of_invariant
    (P := fun h ↦ h = History.nil (splitHeads.initInput ([] : List (Option Bool))) ∨
      splitHeads.Halted h ∧ h.space ≤ 2)
  · exact Or.inl rfl
  · intro c hc d hd
    rcases hc with rfl | ⟨hh, hs⟩
    · change d ∈ (_ ::ₘ _ ::ₘ (0 : Multiset _)) at hd
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hd
      rcases hd with rfl | rfl <;> exact Or.inr ⟨rfl, by decide⟩
    · rw [splitHeads.stepWith_of_halted Multiset c hh] at hd
      obtain rfl := Multiset.mem_singleton.mp hd
      exact Or.inr ⟨hh, hs⟩
  · intro c hc
    rcases hc with rfl | ⟨_, hs⟩
    · decide
    · exact hs

-- Branches return to the same blank configuration while retaining different visit intervals.
def rejoinHeads : NTM Unit Bool (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ i :=
    { inputMove := 0
      work := fun _ => (none,
        if q = 0 then (if i = 0 then -1 else 1) else if q = 1 then 1 else -1)
      output := none
      state := if q = 0 then (if i = 0 then 1 else 2) else 3 }

#guard (rejoinHeads.runWith (TM.Cfg Unit Bool (Fin 4) #[]) Multiset ([] : List Bool) 2).map
  (fun c => (c.state, c.workPos ())) = ↑([(3, 0), (3, 0), (3, 0), (3, 0)] : List (Fin 4 × ℤ))
#guard (rejoinHeads.runHistoryWith (TM.Cfg Unit Bool (Fin 4) #[]) Multiset ([] : List Bool) 2).map
  (fun c => ((c.visited ()).fst, (c.visited ()).snd)) = ↑([(-1, 0), (-1, 0), (0, 1), (0, 1)] : List (ℤ × ℤ))

-- An early accepting branch does not excuse another branch missing the time bound.
def mixed : NTM (Fin 0) (Option Bool) (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q o i := if q = 0 ∧ i = 0 then ⟨0, Fin.elim0, none, 0⟩
    else guess.transition q o i

example : mixed.Accepts (.ofList []) := by
  have hm : (3, #[some true, some false, some false]) ∈
      (mixed.runWith (TM.Cfg (Fin 0) (Option Bool) (Fin 4) #[])
        Multiset ([] : List (Option Bool)) 3).map (fun c => (c.state, c.output)) := by decide
  obtain ⟨c, hc, h⟩ := Multiset.mem_map.mp hm
  refine ⟨3, c, hc, ?_, congrArg Prod.snd h⟩
  change (c.state == 3) = true
  simp [show c.state = 3 from congrArg Prod.fst h]

example : ¬mixed.UsesTime [] 3 := by
  intro h
  have hm : 0 ∈ (mixed.runWith (TM.Cfg (Fin 0) (Option Bool) (Fin 4) #[])
      Multiset ([] : List (Option Bool)) 3).map (·.state) := by decide
  obtain ⟨c, hc, he⟩ := Multiset.mem_map.mp hm
  have hh := h c hc
  change (c.state == 3) = true at hh
  simp [he] at hh

-- Space alone is meaningful for divergence, but an NSPACE decider must terminate.
def forever : TM Id (Fin 0) (Option Bool) Unit where
  q₀ := ()
  halt _ := false
  transition _ _ := pure <| ⟨0, Fin.elim0, none, ()⟩

example (xs : List (Option Bool)) : NTM.UsesSpace forever.toBinary xs 0 := by
  intro n c _
  simp [History.space]

private theorem forever_diverges (xs : List (Option Bool)) : ¬NTM.Terminates forever.toBinary xs := by
  rw [TM.terminates_toBinary_iff]
  rintro ⟨n, hn⟩
  exact Bool.false_ne_true hn

example : ¬NTM.DecidesInSpace forever.toBinary (fun _ : List Bool => False) (fun _ => 0) := by
  intro h
  exact forever_diverges _ (h.decides (⌜([] : List Bool)⌝₂) [] (UniqueEncoding.mem_decode_iff.mpr rfl)).1

-- A malformed terminal output cannot silently count as rejection.
def malformed : TM Id (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| { answer false true with output := none }

example : ¬NTM.BooleanOutput malformed.toBinary (.ofList []) := by
  have ht : NTM.UsesTime malformed.toBinary [] 1 :=
    (malformed.usesTime_toBinary_iff _ _).2 rfl
  rw [NTM.booleanOutput_iff_of_usesTime ht]
  intro h
  have hc : malformed.run (TM.Cfg (Fin 0) (Option Bool) Bool #[]) ([] : List (Option Bool)) 1 ∈
      malformed.toBinary.runWith _ Multiset ([] : List (Option Bool)) 1 := by
    simp only [Controller.mem_runWith_toBinary_iff]
  obtain ⟨b, hb⟩ := h _ hc
  cases b <;> cases congrArg Array.size hb

end NondeterministicTest
