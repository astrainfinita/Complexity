/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Specification.History
import Mathlib.Data.Fintype.Option

set_option experimental.vcgen true

open Complexity (TM)
open Complexity.Controller (History)
open Complexity.TM
open Std.WP

namespace ProgramCopyTest

abbrev Symbol := Option Bool

def input (xs : List Bool) : Array Symbol := (xs.map some).toArray

def body : TM.Program (Fin 0) Symbol Bool := do
  let a ← Program.readInput
  if a = none then
    pure true
  else
    Program.emit a
    Program.moveInput 1
    pure false

def copyInput : TM.Program (Fin 0) Symbol Unit := Program.repeatUntil body

example : Finite (copyInput.State ⊕ copyInput.Exit) := inferInstance

private theorem cfg_ext {xs : Array Symbol} (s t : Cfg (Fin 0) Symbol Unit xs)
    (hi : s.inputPos = t.inputPos) (ho : s.output = t.output) : s = t := by
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · exact hi
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · exact ho

private def state (xs : List Bool) (i : ℕ) (h : i ≤ xs.length) :
    Cfg (Fin 0) Symbol Unit (input xs) :=
  { (rawExecution (input xs).toList).init () with
    inputPos := ⟨i + 1, by simp only [input, List.size_toArray, List.length_map]; omega⟩
    output := input (xs.take i) }

private theorem at_input_lt (xs : List Bool) (i : ℕ) (h : i < xs.length) :
    (state xs i h.le).inputSymbol = .some xs[i] := by
  simp [state, Cfg.inputSymbol, input, List.getElem?_eq_getElem h]

private theorem at_input_end (xs : List Bool) :
    (state xs xs.length le_rfl).inputSymbol = none := by
  simp [state, Cfg.inputSymbol, input]
  rfl

private theorem at_step (xs : List Bool) (i : ℕ) (h : i < xs.length) :
    apply { Program.idle (κ := Fin 0) (Γ := Symbol) with inputMove := 1 }
      (apply { Program.idle (κ := Fin 0) (Γ := Symbol) with output := some (.some xs[i]) }
        (state xs i h.le)) = state xs (i + 1) h := by
  apply cfg_ext
  · simp only [apply_inputPos]
    apply Fin.ext
    simp [Program.idle, state, moveInputPos, input]
    omega
  · change (input (xs.take i)).push (.some xs[i]) = input (xs.take (i + 1))
    apply Array.toList_inj.mp
    simp only [input, Array.toList_push, List.toList_toArray,
      List.take_succ_eq_append_getElem h, List.map_append, List.map_cons, List.map_nil]

private def Inv (xs : List Bool)
    (s : History (Cfg (Fin 0) Symbol Unit (input xs)) (Action (Fin 0) Symbol Unit)) (b : ℕ) : Prop :=
  ∃ i h, s.last = state xs i h ∧ b = 4 * (xs.length - i) + 2

private theorem inv_done (xs : List Bool)
    {s : History (Cfg (Fin 0) Symbol Unit (input xs)) (Action (Fin 0) Symbol Unit)}
    {b : ℕ} (h : Inv xs s b) (ha : s.last.inputSymbol = none) :
    s.last.output = input xs ∧ s.space ≤ 0 := by
  obtain ⟨i, hi, hs, _⟩ := h
  rw [hs] at ha
  have he : i = xs.length := by
    by_contra hn
    have hl : i < xs.length := by omega
    rw [at_input_lt xs i hl] at ha
    contradiction
  subst i
  simp [hs, state, History.space]

private theorem inv_next (xs : List Bool)
    {s : History (Cfg (Fin 0) Symbol Unit (input xs)) (Action (Fin 0) Symbol Unit)}
    {b : ℕ} (h : Inv xs s (b + 1)) (ha : s.last.inputSymbol ≠ none) :
    Inv xs (apply { Program.idle (κ := Fin 0) (Γ := Symbol) with inputMove := 1 }
      (apply { Program.idle (κ := Fin 0) (Γ := Symbol) with output := some s.last.inputSymbol } s))
      (b - 3) := by
  obtain ⟨i, hi, hs, hb⟩ := h
  rw [hs] at ha
  have hl : i < xs.length := by
    by_contra hn
    have he : i = xs.length := by omega
    subst i
    exact ha (at_input_end xs)
  refine ⟨i + 1, hl, ?_, by omega⟩
  simpa only [History.apply_last, hs, at_input_lt xs i hl] using at_step xs i hl

private theorem inv_budget (xs : List Bool)
    {s : History (Cfg (Fin 0) Symbol Unit (input xs)) (Action (Fin 0) Symbol Unit)}
    {b : ℕ} (h : Inv xs s (b + 1)) (ha : s.last.inputSymbol ≠ none) : 4 < b := by
  obtain ⟨i, hi, hs, hb⟩ := h
  rw [hs] at ha
  have hn : i ≠ xs.length := by
    intro he
    subst i
    exact ha (at_input_end xs)
  omega

private theorem body_spec (xs : List Bool) :
    Triple (body.verify (Program.semantics (input xs)))
      (fun s b ↦ Inv xs s (b + 1))
      (fun r s b ↦ if r then s.last.output = input xs ∧ s.space ≤ 0 else Inv xs s b) () := by
  unfold body
  vcgen
  case vc1 =>
    rename_i s b hs a t c hr ha
    rcases hr with ⟨rfl, rfl, rfl⟩
    simpa [History.space] using inv_done xs hs ha
  case vc2 =>
    rename_i s b hs a t c hr ha u v d he w z f hm
    rcases hr with ⟨rfl, rfl, rfl⟩
    rcases he with ⟨rfl, rfl, rfl⟩
    rcases hm with ⟨rfl, rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    simpa [Inv, Nat.sub_sub] using inv_next xs hs ha
  case vc3 =>
    rename_i s b hs a t c hr ha u v d he
    rcases hr with ⟨rfl, rfl, rfl⟩
    rcases he with ⟨rfl, rfl, rfl⟩
    have := inv_budget xs hs ha
    omega
  case vc4 =>
    rename_i s b hs a t c hr ha
    rcases hr with ⟨rfl, rfl, rfl⟩
    have := inv_budget xs hs ha
    omega
  case vc5 =>
    rename_i s b hs
    obtain ⟨i, hi, he, hb⟩ := hs
    omega

private theorem copy_spec (xs : List Bool) :
    Triple (copyInput.verify (Program.semantics (input xs))) (Inv xs)
      (fun _ s _ ↦ s.last.output = input xs ∧ s.space ≤ 0) () := by
  unfold copyInput
  apply Program.spec_repeatUntil
  · intro s b hs
    simpa [Inv] using hs
  · rintro s b ⟨i, hi, he, rfl⟩
    omega
  · exact body_spec xs

-- The same finite controller copies every input length; bits remain distinct from blank.
theorem copyInput_computesInTimeAndSpace (xs : List Bool) :
    (Program.compile copyInput).ComputesInTimeAndSpace
      (input xs).toList (input xs).toList (4 * xs.length + 2) 0 := by
  apply Program.computesInTimeAndSpace (copy_spec xs)
  refine ⟨0, Nat.zero_le _, ?_, by simp⟩
  apply cfg_ext <;> rfl

end ProgramCopyTest
