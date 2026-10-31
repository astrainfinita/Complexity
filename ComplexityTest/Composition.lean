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
    (a.isNone,
      { inputMove := if a.isSome then 1 else 0
        work := fun i ↦ Fin.elim0 i
        output := if a.isSome then some a else none })

private def scanned (xs : List Bool) (n : ℕ) (hn : n ≤ xs.length) : Cfg (Fin 0) Symbol (input xs) where
  inputPos := ⟨n + 1, by simp only [input, List.size_toArray, List.length_map]; omega⟩
  workTapes := fun i ↦ Fin.elim0 i
  workPos := fun i ↦ Fin.elim0 i
  output := input (xs.take n)

private theorem at_zero (xs : List Bool) :
    (false, scanned xs 0 (Nat.zero_le _)) = copier.init (xs.map some) := by
  refine Prod.ext rfl ?_
  apply Cfg.ext
  · rfl
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · simp [scanned, input]

private theorem at_read (xs : List Bool) (n : ℕ) (hn : n ≤ xs.length) :
    (scanned xs n hn).inputSymbol = xs[n]? := by
  simp only [scanned, Cfg.inputSymbol, input, List.getElem?_toArray, List.getElem?_map]
  cases xs[n]? <;> rfl

private theorem step_at (xs : List Bool) (n : ℕ) (hn : n < xs.length) :
    copier.step (false, scanned xs n hn.le) = (false, scanned xs (n + 1) hn) := by
  have hr := at_read xs n hn.le
  rw [List.getElem?_eq_getElem hn] at hr
  simp only [TM.step_eq, id_eq, Bool.false_eq_true, ↓reduceIte, copier, hr, Option.isSome_some,
    Option.isNone_some, Id.run_pure, Controller.apply_prod, Prod.mk.injEq, true_and]
  apply Cfg.ext
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
    copier.run (xs.map some) n = (false, scanned xs n hn) := by
  induction n with
  | zero => exact (at_zero xs).symm
  | succ n ih =>
    rw [Controller.run_succ]
    rw [ih (by omega), step_at xs n (by omega)]

def copied (xs : List Bool) : Bool × Cfg (Fin 0) Symbol (input xs) :=
  (true, scanned xs xs.length le_rfl)

theorem run_copier (xs : List Bool) : copier.run (xs.map some) (xs.length + 1) = copied xs := by
  rw [Controller.run_succ]
  rw [run_at xs xs.length le_rfl]
  have hr : (scanned xs xs.length le_rfl).inputSymbol = none := by rw [at_read]; simp
  simp only [TM.step_eq, Bool.false_eq_true, ↓reduceIte, copier, hr,
    Option.isSome_none, Option.isNone_none, Controller.apply_prod]
  refine Prod.ext rfl ?_
  apply Cfg.ext
  · rfl
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · rfl

@[simp] theorem copied_output (xs : List Bool) : (copied xs).2.output = input xs := by
  simp [copied, scanned]

theorem copier_halts (xs : List Bool) : copier.Halted (copier.run (xs.map some) (xs.length + 1)) := by
  rw [run_copier]
  rfl

#guard (copier.run (([] : List Bool).map some) 1).2.output == input []
#guard (copier.run (([false] : List Bool).map some) 2).2.output == input [false]
#guard (copier.run (([false, true] : List Bool).map some) 3).2.output == input [false, true]

end CompositionTest
