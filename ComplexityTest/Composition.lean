/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Data.Embedding
meta import Complexity.Control.Transition.Basic
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Syntax
meta import Complexity.Data.IntMemory.Basic
meta import Complexity.Data.NatMemory

import Mathlib.Basic.Finite.Prod
import Complexity.Models.TuringMachine.Program.Call
import Complexity.Models.TuringMachine.Program.Specification.History

set_option experimental.vcgen true

open Complexity Complexity.TM Std.WP

namespace CompositionTest

abbrev Symbol := Option Bool

abbrev input (xs : List Bool) : Array Symbol := (xs.map some).toArray

-- One transition copies each data bit; a separate transition halts on the end blank.
def copier : TM Id (Fin 0) Symbol Bool where
  q₀ := false
  halt := id
  transition := fun _ (a, _) ↦ pure <|
    { inputMove := if a.isSome then 1 else 0
      work := fun i ↦ Fin.elim0 i
      output := if a.isSome then some a else none
      state := a.isNone }

private def scanned (xs : List Bool) (n : ℕ) (hn : n ≤ xs.length) : Cfg (Fin 0) Symbol Bool (input xs) where
  state := false
  inputPos := ⟨n + 1, by simp only [input, List.size_toArray, List.length_map]; omega⟩
  workTapes := fun i ↦ Fin.elim0 i
  workPos := fun i ↦ Fin.elim0 i
  output := input (xs.take n)

private theorem at_zero (xs : List Bool) : scanned xs 0 (Nat.zero_le _) = (copier.initInput (Config := Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some)) := by
  apply Cfg.ext
  · rfl
  · rfl
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · simp [scanned, input]

private theorem at_read (xs : List Bool) (n : ℕ) (hn : n ≤ xs.length) :
    (scanned xs n hn).inputSymbol = xs[n]? := by
  simp only [scanned, Cfg.inputSymbol, input, List.getElem?_toArray, List.getElem?_map]
  cases xs[n]? <;> rfl

private theorem step_at (xs : List Bool) (n : ℕ) (hn : n < xs.length) :
    copier.step (scanned xs n hn.le) = scanned xs (n + 1) hn := by
  have hr := at_read xs n hn.le
  rw [List.getElem?_eq_getElem hn] at hr
  simp only [TM.step_eq, ↓reduceIte, copier, hr, Option.isSome_some, Option.isNone_some]
  change apply _ (scanned xs n hn.le) = _
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp [scanned, Input.movePos, input]
    omega
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · change (input (xs.take n)).push (some xs[n]) = input (xs.take (n + 1))
    apply Array.toList_inj.mp
    simp only [input, Array.toList_push,
      List.take_succ_eq_append_getElem hn, List.map_append,
      List.map_cons, List.map_nil]

private theorem run_at (xs : List Bool) (n : ℕ) (hn : n ≤ xs.length) :
    copier.run (Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some) n = scanned xs n hn := by
  induction n with
  | zero => exact (at_zero xs).symm
  | succ n ih =>
    rw [Controller.run_succ]
    rw [ih (by omega), step_at xs n (by omega)]

def copied (xs : List Bool) : Cfg (Fin 0) Symbol Bool (input xs) :=
  { scanned xs xs.length le_rfl with state := true }

theorem run_copier (xs : List Bool) : copier.run (Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1) = copied xs := by
  rw [Controller.run_succ]
  rw [run_at xs xs.length le_rfl]
  have hr : (scanned xs xs.length le_rfl).inputSymbol = none := by rw [at_read]; simp
  simp only [TM.step_eq, Bool.false_eq_true, ↓reduceIte, copier, hr,
    Option.isSome_none, Option.isNone_none]
  apply Cfg.ext
  · rfl
  · rfl
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · rfl

@[simp] theorem copied_output (xs : List Bool) : (copied xs).output = input xs := by
  simp [copied, scanned]

theorem copier_halts (xs : List Bool) : copier.Halted (copier.run (Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1)) := by
  rw [run_copier]
  rfl

#guard (copier.run (Cfg (Fin 0) Symbol Bool ([].map some).toArray) (([] : List Bool).map some) 1).output == input []
#guard (copier.run (Cfg (Fin 0) Symbol Bool ([false].map some).toArray) (([false] : List Bool).map some) 2).output == input [false]
#guard (copier.run (Cfg (Fin 0) Symbol Bool ([false, true].map some).toArray) (([false, true] : List Bool).map some) 3).output == input [false, true]

end CompositionTest
