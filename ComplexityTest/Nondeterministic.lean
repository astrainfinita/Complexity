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
import Complexity.Control.Controller.Binary
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
example : (fixedOutputs 0).NDecidableWithin
    (fun _ : List Bool => False) (fun _ => 0) (fun _ => 0) := by
  refine ⟨_, rfl, fun _ _ _ => ⟨0, rfl, ?_, ?_⟩⟩ <;> simp

example : ¬(fixedOutputs 0).NDecidableWithin
    (fun _ : List Bool => True) (fun _ => 0) (fun _ => 0) := by
  rintro ⟨R, rfl, h⟩
  obtain ⟨ys, rfl, _, h⟩ := h [] (encode (RawWord Bool) ([] : List Bool)) (by simp)
  simp at h

-- Even alongside a valid accepting result, a malformed branch invalidates the decision.
example : ¬(fixedOutputs {RawWord.ofList [], ⌜true⌝₂}).NDecidableWithin
    (fun _ : List Bool => True) (fun _ => 0) (fun _ => 0) := by
  rintro ⟨R, rfl, h⟩
  obtain ⟨ys, rfl, hb, _⟩ := h [] (encode (RawWord Bool) ([] : List Bool)) (by simp)
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (hb (RawWord.ofList []) (by simp))
  have he := UniqueEncoding.mem_decode_iff.mp hb
  cases b <;> cases he

def answer {Q : Type} (b : Bool) (q : Q) : Q × TM.Action (Fin 0) (Option Bool) :=
  (q, { inputMove := 0, work := Fin.elim0, output := some (some b) })

-- One branch rejects immediately; the other finishes the three-bit code for true.
def guess : NTM (Fin 0) (Option Bool) (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ i :=
    if q = 0 then if i = 0 then answer false 3 else answer true 1
    else answer false (if q = 1 then 2 else 3)

private theorem guess_results (xs : List (Option Bool)) :
    (guess.runWith Multiset xs 3).map (fun c => (c.1, c.2.output)) =
      ↑([(3, #[some false]), (3, #[some true, some false, some false]),
        (3, #[some true, some false, some false]), (3, #[some true, some false, some false]),
        (3, #[some true, some false, some false])] : List (Fin 4 × Array (Option Bool))) := rfl

private theorem guess_time (xs : List (Option Bool)) :
    ∀ c ∈ guess.runWith Multiset xs 3, guess.Halted c := by
  intro c hc
  have hm := Multiset.mem_map_of_mem (fun c => (c.1, c.2.output)) hc
  rw [guess_results] at hm
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false, or_self,
    Prod.mk.injEq] at hm
  rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [Controller.Halted, guess, h]

private theorem guess_boolean (xs : RawWord Bool) : guess.BooleanOutput xs := by
  rw [NTM.booleanOutput_iff_of_forall_halted (guess_time _)]
  intro c hc
  have hm := Multiset.mem_map_of_mem (fun c => (c.1, c.2.output)) hc
  rw [guess_results] at hm
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false, or_self,
    Prod.mk.injEq] at hm
  rcases hm with ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

private theorem guess_accepts (xs : RawWord Bool) : guess.Accepts xs := by
  rw [NTM.accepts_iff_of_forall_halted (guess_time _)]
  have hm : (3, #[some true, some false, some false]) ∈
      (guess.runWith Multiset (xs.toList.map some) 3).map
        (fun c => (c.1, c.2.output)) := by rw [guess_results]; simp
  obtain ⟨c, hc, h⟩ := Multiset.mem_map.mp hm
  exact ⟨c, hc, congrArg Prod.snd h⟩

theorem guess_spec : guess.DecidesWithin (fun _ : List Bool => True)
    (fun _ => 3) (fun _ => 0) := by
  intro xs a ha
  refine ⟨fun h hh ↦ ⟨guess.length_le_of_forall_halted Multiset (xs.toList.map some)
    (guess_time _) h hh, ?_⟩, guess_boolean _, iff_true_intro (guess_accepts _)⟩
  simp [History.space]

private theorem guess_size_spec : TimeSpaceModel.ntm.NDecidableWithinBySize
    (fun _ : List Bool => True) (fun _ => 3) (fun _ => 0) :=
  guess_spec.nDecidableWithin

example : (fun _ : List Bool => True) ∈ NTISP .ntm (fun _ => 3) (fun _ => 0) :=
  guess_size_spec.mem_ntisp

example : (fun _ : List Bool => True) ∈ NP .ntm := by
  apply NP.of_time_le guess_size_spec.mem_ntime 3 0
  simp

example : (fun _ : List Bool => True) ∈ NSPACE .ntm (fun _ => 0) :=
  guess_size_spec.mem_nspace

-- Changing the predicate and budget preserves every accepting and rejecting branch.
-- Only the final comparison with O(n) excludes n=0; the machine still terminates there.
example : (fun xs : List Bool => xs = xs) ∈ NTISP .ntm id (fun _ => 0) := by
  have h : TimeSpaceModel.ntm.NDecidableWithinBySize
      (fun xs : List Bool => xs = xs) (fun n => n + 3) (fun _ => 0) :=
    (guess_size_spec.mono (fun n => by omega) (fun _ => le_rfl)).congr (fun _ => by simp)
  exact h.mem_ntisp_of_dominated
    (dominatedAtTop_iff.mpr ⟨4, 1, fun n hn => by dsimp; omega⟩) (DominatedAtTop.refl _)

-- A space-only machine proof supplies its implicit time bound through the model bridge.
example : ∃ t, TimeSpaceModel.ntm.NDecidableWithin (fun _ : List Bool => True) t (fun _ => 0) :=
  ⟨_, guess_spec.nDecidableWithin⟩

-- The two branches visit [-1,0] and [0,1]: each uses two cells.
def splitHeads : NTM (Fin 1) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ i :=
    (true,
      { inputMove := 0, work := fun _ => (none, if i = 0 then -1 else 1)
        output := some (some (i == 1)) })

#guard (splitHeads.runHistoryWith
  Multiset ([] : List (Option Bool)) 1).map (fun h ↦ h.snd.space) = ↑[2, 2]
#guard (splitHeads.runHistoryWith
  Multiset ([] : List (Option Bool)) 4).map (fun h ↦ h.snd.space) = ↑[2, 2]

-- A local invariant proves the space bound at every depth, including halted padding.
-- Guards that the generic `Controller.forall_mem_histories` applies with a step condition stated
-- on the members of a `Multiset`.
example : ∀ h ∈ splitHeads.histories Multiset ([] : List (Option Bool)), h.snd.space ≤ 2 := by
  intro h hmem
  have hP := splitHeads.forall_mem_histories Multiset ([] : List (Option Bool))
    (P := fun h ↦ h = History.nil (splitHeads.init ([] : List (Option Bool))) ∨
      splitHeads.Halted h ∧ h.snd.space ≤ 2) (Or.inl rfl) ?_ h hmem
  · rcases hP with rfl | ⟨_, hs⟩
    · decide
    · exact hs
  · intro c hc d hd
    rcases hc with rfl | ⟨hh, hs⟩
    · change d ∈ (_ ::ₘ _ ::ₘ (0 : Multiset _)) at hd
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hd
      rcases hd with rfl | rfl <;> exact Or.inr ⟨rfl, by decide⟩
    · rw [splitHeads.stepWith_of_halted Multiset c hh] at hd
      obtain rfl := Multiset.mem_singleton.mp hd
      exact Or.inr ⟨hh, hs⟩

-- Branches return to the same blank configuration while retaining different visit intervals.
def rejoinHeads : NTM Unit Bool (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ i :=
    (if q = 0 then (if i = 0 then 1 else 2) else 3,
      { inputMove := 0
        work := fun _ => (none,
          if q = 0 then (if i = 0 then -1 else 1) else if q = 1 then 1 else -1)
        output := none })

#guard (rejoinHeads.runWith Multiset ([] : List Bool) 2).map
  (fun c => (c.1, c.2.workPos ())) = ↑([(3, 0), (3, 0), (3, 0), (3, 0)] : List (Fin 4 × ℤ))
#guard (rejoinHeads.runHistoryWith Multiset ([] : List Bool) 2).map
  (fun h => let v := h.snd.visited (); (v.fst, v.snd)) =
    ↑([(-1, 0), (-1, 0), (0, 1), (0, 1)] : List (ℤ × ℤ))

-- An early accepting branch does not excuse another branch missing the time bound.
def mixed : NTM (Fin 0) (Option Bool) (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q o i := if q = 0 ∧ i = 0 then (0, ⟨0, Fin.elim0, none⟩)
    else guess.transition q o i

example : mixed.Accepts (.ofList []) := by
  have hm : (3, #[some true, some false, some false]) ∈
      (mixed.runWith
        Multiset ([] : List (Option Bool)) 3).map (fun c => (c.1, c.2.output)) := by decide
  obtain ⟨c, hc, h⟩ := Multiset.mem_map.mp hm
  refine ⟨3, c, hc, ?_, congrArg Prod.snd h⟩
  simp [Controller.Halted, mixed, show c.1 = 3 from congrArg Prod.fst h]

example : ¬∀ h ∈ mixed.histories Multiset ([] : List (Option Bool)), h.length ≤ 3 := by
  intro h
  have hm : 0 ∈ (mixed.runWith Multiset ([] : List (Option Bool)) 4).map (·.1) := by decide
  obtain ⟨c, hc, he⟩ := Multiset.mem_map.mp hm
  have hh := mixed.forall_halted_succ_of_forall_length_le Multiset ([] : List (Option Bool)) h c hc
  simp [Controller.Halted, mixed, he] at hh

-- Space alone is meaningful for divergence, but an NSPACE decider must terminate.
def forever : TM Id (Fin 0) (Option Bool) Unit where
  q₀ := ()
  halt _ := false
  transition _ _ := pure <| ((), ⟨0, Fin.elim0, none⟩)

example (xs : List (Option Bool)) :
    ∀ h ∈ forever.toBinary.histories Multiset xs, h.snd.space ≤ 0 := by
  intro c _
  simp [History.space]

private theorem forever_diverges (xs : List (Option Bool)) :
    ¬∃ t, ∀ h ∈ forever.toBinary.histories Multiset xs, h.length ≤ t := by
  rintro ⟨t, ht⟩
  exact Bool.false_ne_true <| (forever.forall_halted_runWith_toBinary_iff xs (t + 1)).1 <|
    forever.toBinary.forall_halted_succ_of_forall_length_le Multiset xs ht

example : ¬∃ t, NTM.DecidesWithin forever.toBinary
    (fun _ : List Bool => False) t (fun _ => 0) := by
  rintro ⟨t, h⟩
  exact forever_diverges _ ⟨_, fun c hc ↦
    ((h (encode (RawWord Bool) ([] : List Bool)) [] (by simp)).1 c hc).1⟩

-- A malformed terminal output cannot silently count as rejection.
def malformed : TM Id (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (true, { (answer false true).2 with output := none })

example : ¬NTM.BooleanOutput malformed.toBinary (.ofList []) := by
  have ht := (malformed.forall_halted_runWith_toBinary_iff ([] : List (Option Bool)) 1).2 rfl
  rw [NTM.booleanOutput_iff_of_forall_halted ht]
  intro h
  have hc : malformed.run ([] : List (Option Bool)) 1 ∈
      malformed.toBinary.runWith Multiset ([] : List (Option Bool)) 1 := by
    simp only [Controller.mem_runWith_toBinary_iff]
  obtain ⟨b, hb⟩ := h _ hc
  cases b <;> cases congrArg Array.size hb

-- Refactoring through a common coding predicate preserves the complete old quantifiers:
-- the behavior is fixed before all inputs, and both budgets constrain the same outputs.
section ClassSemantics

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
  (model : TimeSpaceModel Multiset Data) (p : α → Prop) (T S : ℕ → ℕ)

example : p ∈ NTISP model T S ↔
    ∃ t s, (∃ R ∈ model.behaviors, ∀ src a,
      a ∈ decode α src → ∃ outs,
        R src outs (t (model.inputSize src))
          (s (model.inputSize src)) ∧
        (∀ dst ∈ outs, (decode Bool dst).Dom) ∧
        ((∃ dst ∈ outs, true ∈ decode Bool dst) ↔ p a)) ∧
      DominatedAtTop t T ∧ DominatedAtTop s S := by
  constructor
  · rintro ⟨t, s, ⟨R, hb, h⟩, ht, hs⟩
    exact ⟨t, s, ⟨R, hb, fun src a => h a src⟩, ht, hs⟩
  · rintro ⟨t, s, ⟨R, hb, h⟩, ht, hs⟩
    exact ⟨t, s, ⟨R, hb, fun a src => h src a⟩, ht, hs⟩

-- The unmeasured resource remains a function of input length, outside the input quantifier.
example : p ∈ NTIME model T ↔
    ∃ t, (∃ s : ℕ → ℕ, ∃ R ∈ model.behaviors, ∀ src a,
      a ∈ decode α src → ∃ outs,
        R src outs (t (model.inputSize src))
          (s (model.inputSize src)) ∧
        (∀ dst ∈ outs, (decode Bool dst).Dom) ∧
        ((∃ dst ∈ outs, true ∈ decode Bool dst) ↔ p a)) ∧
      DominatedAtTop t T := by
  constructor
  · rintro ⟨t, ⟨s, R, hb, h⟩, ht⟩
    exact ⟨t, ⟨s, R, hb, fun src a => h a src⟩, ht⟩
  · rintro ⟨t, ⟨s, R, hb, h⟩, ht⟩
    exact ⟨t, ⟨s, R, hb, fun a src => h src a⟩, ht⟩

example : p ∈ NSPACE model S ↔
    ∃ s, (∃ t : ℕ → ℕ, ∃ R ∈ model.behaviors, ∀ src a,
      a ∈ decode α src → ∃ outs,
        R src outs (t (model.inputSize src))
          (s (model.inputSize src)) ∧
        (∀ dst ∈ outs, (decode Bool dst).Dom) ∧
        ((∃ dst ∈ outs, true ∈ decode Bool dst) ↔ p a)) ∧
      DominatedAtTop s S := by
  constructor
  · rintro ⟨s, ⟨t, R, hb, h⟩, hs⟩
    exact ⟨s, ⟨t, R, hb, fun src a => h a src⟩, hs⟩
  · rintro ⟨s, ⟨t, R, hb, h⟩, hs⟩
    exact ⟨s, ⟨t, R, hb, fun a src => h src a⟩, hs⟩

end ClassSemantics

end NondeterministicTest
