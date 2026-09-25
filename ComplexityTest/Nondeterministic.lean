/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.NP
import Complexity.Models.TuringMachine.Nondeterministic.Deterministic
meta import Complexity.Models.TuringMachine.Nondeterministic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Controller
meta import Complexity.Control.Choice
meta import Complexity.Control.Transition
meta import Complexity.Data.IntMemory

open Complexity
open TM (apply)

namespace NondeterministicTest

def answer (b : Bool) : TM.Action (Fin 0) (Option Bool) Bool where
  inputMove := 0
  work := Fin.elim0
  output := some (some b)
  state := true

-- One branch rejects, the other accepts: acceptance must be existential.
def guess : NTM (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ i := answer (i == 1)

private theorem guess_run_one (xs : List (Option Bool)) :
    guess.runWith (TM.Cfg (Fin 0) (Option Bool) Bool xs.toArray)
      Choice.binaryMultiset xs 1 =
      ↑[apply (answer false)
          (guess.initInput (Config := TM.Cfg (Fin 0) (Option Bool) Bool xs.toArray) xs),
        apply (answer true)
          (guess.initInput (Config := TM.Cfg (Fin 0) (Option Bool) Bool xs.toArray) xs)] := rfl

private theorem guess_time (xs : List (Option Bool)) : guess.UsesTime xs 1 := by
  intro c hc
  rw [guess_run_one] at hc
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

private theorem guess_boolean (xs : List (Option Bool)) : guess.BooleanOutput xs := by
  rw [NTM.booleanOutput_iff_of_usesTime (guess_time xs)]
  intro c hc
  rw [guess_run_one] at hc
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

private theorem guess_accepts (xs : List (Option Bool)) : guess.Accepts xs := by
  rw [NTM.accepts_iff_of_usesTime (guess_time xs), guess_run_one]
  exact ⟨_, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _), rfl⟩

theorem guess_spec : guess.DecidesInTimeAndSpace (fun _ : List Bool => True)
    (fun _ => 1) (fun _ => 0) := by
  refine ⟨⟨?_, fun xs _ _ => guess_time _⟩, ?_⟩
  · intro xs _ _
    exact ⟨(guess_time _).terminates, guess_boolean _, iff_true_intro (guess_accepts _)⟩
  · intro xs _ _ n cs _
    simp [TM.spaceUsedOfTrace]

example : (fun _ : List Bool => True) ∈ NTISP (fun _ => 1) (fun _ => 0) :=
  NTISP.of_decidableInTimeAndSpace guess_spec.decidableInTimeAndSpace

example : (fun _ : List Bool => True) ∈ NP := by
  apply NP.of_time_le guess_spec.decidesInTime.decidableInTime 1 0
  simp

-- The two branches visit {0,-1} and {0,1}: each uses two cells, not their union's three.
def splitHeads : NTM (Fin 1) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ i :=
    { inputMove := 0, work := fun _ => (none, if i = 0 then -1 else 1)
      output := some (some (i == 1)), state := true }

#guard ((splitHeads.runTraceWith Choice.binaryMultiset
  (splitHeads.initInput (Input := List (Option Bool)) (Config := TM.Cfg (Fin 1) (Option Bool) Bool [].toArray) []) 1).map TM.spaceUsedOfTrace) = ↑[2, 2]
#guard ((splitHeads.runTraceWith Choice.binaryMultiset
  (splitHeads.initInput (Input := List (Option Bool)) (Config := TM.Cfg (Fin 1) (Option Bool) Bool [].toArray) []) 4).map TM.spaceUsedOfTrace) = ↑[2, 2]

-- An early accepting branch does not excuse another branch missing the time bound.
def mixed : NTM (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ i := if i = 0 then ⟨0, Fin.elim0, none, false⟩ else answer true

example : mixed.Accepts [] :=
  ⟨1, apply (answer true)
    (mixed.initInput (Config := TM.Cfg (Fin 0) (Option Bool) Bool #[]) ([] : List (Option Bool))),
    Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _), rfl, rfl⟩

example : ¬mixed.UsesTime [] 1 := by
  intro h
  have hc : apply
      (⟨0, Fin.elim0, none, false⟩ : TM.Action (Fin 0) (Option Bool) Bool)
      (mixed.initInput (Config := TM.Cfg (Fin 0) (Option Bool) Bool #[]) ([] : List (Option Bool))) ∈
      mixed.runWith _ Choice.binaryMultiset ([] : List (Option Bool)) 1 := by
    change _ ∈ (_ ::ₘ _ ::ₘ (0 : Multiset (TM.Cfg (Fin 0) (Option Bool) Bool #[])))
    exact Multiset.mem_cons_self _ _
  exact Bool.false_ne_true (h _ hc)

-- Space alone is meaningful for divergence, but an NSPACE decider must terminate.
def forever : TM Id (Fin 0) (Option Bool) Unit where
  q₀ := ()
  halt _ := false
  transition _ _ := pure <| ⟨0, Fin.elim0, none, ()⟩

example (xs : List (Option Bool)) : NTM.UsesSpace forever.toBinary xs 0 := by
  intro n cs _
  simp [TM.spaceUsedOfTrace]

private theorem forever_diverges (xs : List (Option Bool)) : ¬NTM.Terminates forever.toBinary xs := by
  rw [TM.terminates_toBinary_iff]
  rintro ⟨n, hn⟩
  exact Bool.false_ne_true hn

example : ¬NTM.DecidesInSpace forever.toBinary (fun _ : List Bool => False) (fun _ => 0) := by
  intro h
  exact forever_diverges _ (h.decides [] [] (Part.mem_some [])).1

-- A malformed terminal output cannot silently count as rejection.
def malformed : TM Id (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| { answer false with output := none }

example : ¬NTM.BooleanOutput malformed.toBinary [] := by
  have ht : NTM.UsesTime malformed.toBinary [] 1 :=
    (malformed.usesTime_toBinary_iff _ _).2 rfl
  rw [NTM.booleanOutput_iff_of_usesTime ht]
  intro h
  have hc : malformed.run (TM.Cfg (Fin 0) (Option Bool) Bool #[]) ([] : List (Option Bool)) 1 ∈
      malformed.toBinary.runWith _ Choice.binaryMultiset ([] : List (Option Bool)) 1 := by
    simp only [Controller.mem_runWith_toBinary_iff]
  obtain ⟨b, hb⟩ := h _ hc
  change #[] = #[some b] at hb
  have := congrArg Array.size hb
  simp at this

end NondeterministicTest
