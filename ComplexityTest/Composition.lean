/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.RedirectInput
meta import Complexity.Models.TuringMachine.RedirectOutput
meta import Complexity.Models.TuringMachine.Tapes
meta import Complexity.Data.Embedding
meta import Complexity.Control.Transition
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Word.Configuration
meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory

import Mathlib.Basic.Finite.Prod
import Complexity.Models.TuringMachine.Program.Call
import Complexity.Models.TuringMachine.Program.Specification.Trace
import Complexity.Models.TuringMachine.Program.Word.Configuration
import Complexity.Models.TuringMachine.RedirectInput
import Complexity.Models.TuringMachine.RedirectOutput

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
    simp [scanned, moveInputPos, input]
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

private def bufferEmbedding : (Fin 0 ⊕ Unit) ↪ Fin 1 where
  toFun _ := 0
  inj' := by decide

@[simp] private theorem bufferEmbedding_replace {α : Type*}
    (source : (Fin 0 ⊕ Unit) → α) (target : Fin 1 → α) (j : Fin 1) :
    bufferEmbedding.replace source target j = source (.inr ()) := by
  have hj : j = bufferEmbedding (.inr ()) := Subsingleton.elim _ _
  rw [hj, Function.Embedding.replace_apply]

def toBuffer : TM Id (Fin 1) Symbol Bool := RedirectOutput.compilerAlong bufferEmbedding copier

def fromBuffer : TM Id (Fin 1) Symbol (Bool × Bool) :=
  RedirectInput.compilerAlong bufferEmbedding copier

-- Both calls are compiled into one finite controller, sharing the physical buffer.
def twice : Program (Fin 1) Symbol Unit := do
  let _ ← Program.call toBuffer
  Program.Word.rewind 0
  let _ ← Program.call fromBuffer
  pure ()

private def saved (xs : List Bool) : Cfg (Fin 1) Symbol Unit (input xs) :=
  (RedirectOutput.cfgAlong bufferEmbedding (copied xs) ((rawExecution (xs.map some)).init false)).mapState
    (fun _ ↦ ())

private def rewound (xs : List Bool) : Cfg (Fin 1) Symbol Unit (input xs) :=
  { saved xs with workPos := Function.update (saved xs).workPos 0 0 }

private def finished (xs : List Bool) : Cfg (Fin 1) Symbol Unit (input xs) :=
  { saved xs with output := input xs }

private theorem toBuffer_run (xs : List Bool) :
    toBuffer.run (Cfg (Fin 1) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1) =
      RedirectOutput.cfgAlong bufferEmbedding (copied xs) ((rawExecution (xs.map some)).init false) := by
  change (RedirectOutput.compilerAlong bufferEmbedding copier).run
    (Cfg (Fin 1) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1) = _
  rw [RedirectOutput.run_eq bufferEmbedding, run_copier]
  rfl

private theorem fill_spec (xs : List Bool) (q : ℕ) :
    Triple ((Program.call toBuffer).verify (Program.cfgSemantics (input xs)))
      (fun s b ↦ s = (rawExecution (xs.map some)).init () ∧ xs.length + 1 + q ≤ b)
      (fun _ s b ↦ s = saved xs ∧ q ≤ b) () := by
  have hh : toBuffer.Halted (toBuffer.run (Cfg (Fin 1) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1)) := by
    rw [toBuffer_run]
    rfl
  have hs := Program.cfg_spec_call toBuffer ((toBuffer.initInput (Config := Cfg (Fin 1) Symbol Bool (xs.map some).toArray) (xs.map some)))
    (xs.length + 1) q rfl hh
  constructor
  apply Triple.entails_wp_of_post hs
  intro a s b h
  refine ⟨h.2.1.trans ?_, h.2.2⟩
  change (toBuffer.run (Cfg (Fin 1) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1)).mapState (fun _ ↦ ()) = _
  rw [toBuffer_run]
  rfl

private theorem rewind_spec (xs : List Bool) (q : ℕ) :
    Triple ((Program.Word.rewind 0).verify (Program.cfgSemantics (input xs)))
      (fun s b ↦ s = saved xs ∧ 3 * xs.length + 4 + q ≤ b)
      (fun _ s b ↦ s = rewound xs ∧ q ≤ b) () := by
  apply Program.Word.spec_rewind_cfg_le (saved xs) 0 xs xs.length q
  · simp [saved, RedirectOutput.cfgAlong,
      copied_output, input, Program.Word.tape, IntMemory.ofList]
  · simp [saved, RedirectOutput.cfgAlong,
      copied_output, input]
  · rfl

private theorem read_spec (xs : List Bool) (q : ℕ) :
    Triple ((Program.call fromBuffer).verify (Program.cfgSemantics (input xs)))
      (fun s b ↦ s = rewound xs ∧ xs.length + 1 + q ≤ b)
      (fun _ s b ↦ s = finished xs ∧ q ≤ b) () := by
  let c := RedirectInput.cfgAlong bufferEmbedding xs.toArray (rewound xs)
    ((copier.initInput (Config := Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some))) false
  obtain ⟨l, hl, hr⟩ := RedirectInput.runFrom_init bufferEmbedding copier xs
    (rewound xs) (xs.length + 1)
  change fromBuffer.runFrom c (xs.length + 1) = _ at hr
  rw [show copier.run (Cfg (Fin 0) Symbol Bool (xs.map some).toArray) (xs.map some) (xs.length + 1) = copied xs from
    run_copier xs] at hr
  have hh : fromBuffer.Halted (fromBuffer.runFrom c (xs.length + 1)) := by
    rw [hr]
    rfl
  have hi : c.mapState (fun _ ↦ ()) = rewound xs := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      simp [c, RedirectInput.cfgAlong, RedirectInput.buffer, rewound, saved,
        RedirectOutput.cfgAlong,
        input, RedirectInput.input, copied_output, Fin.eq_zero]
    · funext j
      simp [c, RedirectInput.cfgAlong,
        RedirectInput.position, rewound, Fin.eq_zero]
    · rfl
  have he : (fromBuffer.runFrom c (xs.length + 1)).mapState (fun _ ↦ ()) = finished xs := by
    rw [hr]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      simp [RedirectInput.cfgAlong, RedirectInput.buffer, finished, saved,
        RedirectOutput.cfgAlong,
        input, RedirectInput.input, copied_output, Fin.eq_zero]
    · funext j
      simp [RedirectInput.cfgAlong, RedirectInput.position, finished, saved,
        RedirectOutput.cfgAlong,
        copied, scanned, Fin.eq_zero, input]
    · exact copied_output xs
  have hs := Program.cfg_spec_call fromBuffer c (xs.length + 1) q rfl hh
  rw [hi] at hs
  constructor
  apply Triple.entails_wp_of_post hs
  intro a s b h
  exact ⟨h.2.1.trans he, h.2.2⟩

theorem twice_spec (xs : List Bool) :
    Triple (twice.verify (Program.cfgSemantics (input xs)))
      (fun s b ↦ s = (rawExecution (xs.map some)).init () ∧ 5 * xs.length + 6 ≤ b)
      (fun _ s _ ↦ s = finished xs) () := by
  have h₁ := fill_spec xs ((3 * xs.length + 4) + (xs.length + 1))
  have h₂ := rewind_spec xs (xs.length + 1)
  have h₃ := read_spec xs 0
  unfold twice
  vcgen [h₁, h₂, h₃]
  all_goals simp_all <;> omega

theorem twice_computesInTimeAndSpace (xs : List Bool) :
    (Program.compile twice).ComputesInTimeAndSpace (xs.map some) (xs.map some)
      (5 * xs.length + 6) (5 * xs.length + 7) := by
  have h : Triple (twice.verify (Program.cfgSemantics (input xs)))
      (fun s b ↦ s = (rawExecution (xs.map some)).init () ∧ 5 * xs.length + 6 ≤ b)
      (fun _ s _ ↦ s.output = input xs) () := by
    constructor
    apply Triple.entails_wp_of_post (twice_spec xs)
    intro a s b h
    rw [h]
    rfl
  simpa only [Fintype.card_fin, Nat.one_mul, Nat.add_assoc, input, List.toList_toArray] using
    Program.cfg_computesInTimeAndSpace h ⟨rfl, le_rfl⟩

#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([].map some).toArray) (([] : List Bool).map some) 6).output == input []
#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false].map some).toArray) (([false] : List Bool).map some) 11).output == input [false]
#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false, true].map some).toArray) (([false, true] : List Bool).map some) 16).output == input [false, true]
#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([true, false, true].map some).toArray) (([true, false, true] : List Bool).map some) 21).output == input [true, false, true]
#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false, true].map some).toArray) (([false, true] : List Bool).map some) 16).inputPos.val == 3
#guard (twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false, true].map some).toArray) (([false, true] : List Bool).map some) 16).workPos 0 == 2
#guard ((twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false, true].map some).toArray) (([false, true] : List Bool).map some) 16).workTapes 0)[(0 : ℤ)] == some false
#guard ((twice.compile.run (Cfg (Fin 1) Symbol (twice.State ⊕ twice.Exit) ([false, true].map some).toArray) (([false, true] : List Bool).map some) 16).workTapes 0)[(2 : ℤ)] == none

end CompositionTest
