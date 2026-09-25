/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Tapes
import Complexity.Models.TuringMachine.Program.Call
import Complexity.Models.TuringMachine.Program.Call.Buffered
import Complexity.Control.Program.Loop

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Enumeration
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Transition
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Data.Embedding
meta import Complexity.Models.TuringMachine.Tapes
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Call.Buffered
meta import Complexity.Models.TuringMachine.RedirectInput
meta import Complexity.Models.TuringMachine.RedirectOutput
meta import Complexity.Models.TuringMachine.Program.Enumeration
meta import Complexity.Models.TuringMachine.Program.Tapes

open Complexity Complexity.TM

set_option experimental.vcgen true

namespace ProgramTapesTest

-- Named source tapes occupy reversed, nonconsecutive target coordinates.
def sparse : Bool ↪ Fin 5 where
  toFun b := if b then 1 else 3
  inj' := by decide

def shifted : Fin 5 ↪ Fin 6 where
  toFun i := ⟨i.val + 1, by omega⟩
  inj' := by decide

def input : Array (Option Bool) := #[some false, some true, some false]

def dirty : IntMemory (Option Bool) :=
  (∅ : IntMemory (Option Bool)).set (-3) (some true) |>.set 7 (some false) |>.set 11 (some true)

def sourceTapes (b : Bool) : IntMemory (Option Bool) :=
  if b then (∅ : IntMemory (Option Bool)).set (-2) (some false) |>.set 4 (some true)
  else (∅ : IntMemory (Option Bool)).set 0 (some true) |>.set 1 (some true) |>.set 2 (some false)

def start {n : ℕ} {α : Type} (L : Bool ↪ Fin n)
    (p : TM.Program (Fin n) (Option Bool) α) :
    Cfg (Fin n) (Option Bool) (p.State ⊕ p.Exit) input :=
  { (p.compile.initInput (Config := Cfg (Fin n) _ _ input.toList.toArray) input.toList) with
    inputPos := 2
    workTapes := L.replace sourceTapes (fun _ ↦ dirty)
    workPos := L.replace (fun b ↦ if b then -2 else 0) (fun _ ↦ 7)
    output := #[none, some true] }

def sameTape (a b : IntMemory (Option Bool)) : Bool :=
  (List.range 24).all fun i ↦ a[(i : ℤ) - 6] == b[(i : ℤ) - 6]

def sameData {n : ℕ} {Q Q' : Type}
    (c : Cfg (Fin n) (Option Bool) Q input) (d : Cfg (Fin n) (Option Bool) Q' input) : Bool :=
  c.inputPos == d.inputPos && c.output == d.output &&
    (List.ofFn fun i : Fin n ↦ c.workPos i == d.workPos i &&
      sameTape (c.workTapes i) (d.workTapes i)).all id

-- Returning an infinite-type value must neither require a default nor add a transition.
def pureSource : TM.Program Bool (Option Bool) ℕ := pure 37

def finish {κ : Type} (p : TM.Program κ (Option Bool) ℕ) : TM.Program κ (Option Bool) Unit := do
  let n ← p
  Program.emit (some (decide (n = 37)))

def pureLift := Program.onWork sparse pureSource
def pureThenEmit := finish pureLift

#guard pureLift.compile.halt (start sparse pureLift).state
#guard sameData (start sparse pureLift) (pureLift.compile.runFrom (start sparse pureLift) 0)
#guard !pureThenEmit.compile.halt (start sparse pureThenEmit).state
#guard pureThenEmit.compile.halt (pureThenEmit.compile.runFrom (start sparse pureThenEmit) 1).state
#guard (pureThenEmit.compile.runFrom (start sparse pureThenEmit) 1).output ==
  #[none, some true, some true]

-- A called machine reads both shared input and a selected work tape, then moves both heads.
def called : TM Id Bool (Option Bool) Bool where
  q₀ := false
  halt := id
  transition _ v := pure <|
    { inputMove := 1
      work b := if b then (none, 0) else (some (v.2 true), 1)
      output := some v.1
      state := true }

-- One injection places source work, input, and output in a larger dirty caller bank.
def ports : (Bool ⊕ Bool) ↪ Fin 7 where
  toFun := Sum.elim (fun b ↦ if b then 1 else 5) (fun b ↦ if b then 2 else 4)
  inj' := by decide

def buffered := Program.onWork ports (Program.BufferedCall.program called)

def bufferedStart : Cfg (Fin 7) (Option Bool) (buffered.State ⊕ buffered.Exit) input :=
  { (buffered.compile.initInput (Config := Cfg (Fin 7) _ _ input.toList.toArray) input.toList) with
    inputPos := 2
    workTapes := ports.replace
      (Sum.elim (fun _ ↦ ∅) (fun b ↦ if b then ∅ else RedirectInput.buffer #[true, false]))
      (fun _ ↦ dirty)
    workPos := ports.replace (fun _ ↦ 0) (fun _ ↦ 7)
    output := #[none, some false] }

def bufferedEnd := buffered.compile.runFrom bufferedStart 1

#guard buffered.compile.halt bufferedEnd.state
#guard bufferedEnd.inputPos == bufferedStart.inputPos && bufferedEnd.output == bufferedStart.output
#guard (bufferedEnd.workTapes 2)[(0 : ℤ)] == some true && bufferedEnd.workPos 2 == 1
#guard sameTape (bufferedEnd.workTapes 4) (RedirectInput.buffer #[true, false])
#guard bufferedEnd.workPos 4 == 1 && bufferedEnd.workPos 5 == 1 && bufferedEnd.workPos 1 == 0
#guard ([0, 3, 6] : List (Fin 7)).all fun i ↦
  bufferedEnd.workPos i == 7 && sameTape (bufferedEnd.workTapes i) dirty

def source : TM.Program Bool (Option Bool) ℕ := do
  let _ ← Program.call called
  Program.repeatUntil do
    let a ← Program.read false
    match a with
    | none => pure true
    | some _ => do
      Program.emit a
      Program.move false 1
      pure false
  let a ← Program.readInput
  Program.emit a
  pure 37

def lifted := finish (Program.onWork sparse source)
def liftedEnd := lifted.compile.runFrom (start sparse lifted) 14

-- Call: 1; two continuing loop iterations: 8; stopping iteration: 2; read/emit: 2;
-- the continuation consumes the returned Nat and emits once: 1.
#guard !lifted.compile.halt (lifted.compile.runFrom (start sparse lifted) 13).state
#guard lifted.compile.halt liftedEnd.state
#guard liftedEnd.output == #[none, some true, some true, some true, some false, some false, some true]
#guard liftedEnd.inputPos.val == 3
#guard liftedEnd.workPos 3 == 3 && liftedEnd.workPos 1 == -2
#guard (liftedEnd.workTapes 3)[(0 : ℤ)] == some false
#guard (liftedEnd.workTapes 3)[(1 : ℤ)] == some true
#guard (liftedEnd.workTapes 3)[(2 : ℤ)] == some false
#guard sameTape (liftedEnd.workTapes 1) (sourceTapes true)
#guard ([0, 2, 4] : List (Fin 5)).all fun i ↦
  liftedEnd.workPos i == 7 && sameTape (liftedEnd.workTapes i) dirty

-- Nested embedding preserves both layers of spare tapes and introduces no dispatch steps.
def direct := finish (Program.onWork (sparse.trans shifted) source)
def nested := finish (Program.onWork shifted (Program.onWork sparse source))
def directEnd := direct.compile.runFrom (start (sparse.trans shifted) direct) 14
def nestedEnd := nested.compile.runFrom (start (sparse.trans shifted) nested) 14

#guard !direct.compile.halt
  (direct.compile.runFrom (start (sparse.trans shifted) direct) 13).state
#guard !nested.compile.halt
  (nested.compile.runFrom (start (sparse.trans shifted) nested) 13).state
#guard direct.compile.halt directEnd.state && nested.compile.halt nestedEnd.state
#guard sameData directEnd nestedEnd
#guard directEnd.output == liftedEnd.output && directEnd.inputPos == liftedEnd.inputPos
#guard directEnd.workPos 4 == 3 && directEnd.workPos 2 == -2
#guard sameTape (directEnd.workTapes 4) (liftedEnd.workTapes 3)
#guard ([0, 1, 3, 5] : List (Fin 6)).all fun i ↦
  nestedEnd.workPos i == 7 && sameTape (nestedEnd.workTapes i) dirty

open Std.WP

def localCopy : TM.Program Bool (Option Bool) (Option Bool) := do
  let a ← Program.read true
  Program.write false a
  pure a

-- The local contract mentions only its own two tapes and keeps exact continuation credits.
theorem localCopy_spec {xs : Array (Option Bool)} (c : Cfg Bool (Option Bool) Unit xs)
    (q : ℕ) :
    Triple (localCopy.verify (Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 2 + q)
      (fun a s b ↦ a = c.workSymbols true ∧ s.workSymbols false = a ∧
        s.workTapes true = c.workTapes true ∧ s.workPos = c.workPos ∧
        s.inputPos = c.inputPos ∧ s.output = c.output ∧ b = q) () := by
  unfold localCopy
  vcgen
  all_goals simp_all [Program.idle, Cfg.workSymbols, funext_iff]

-- Reusing the contract needs no finite target bank or assumptions that spare tapes are empty.
theorem localCopy_onWork_spec {τ : Type} [DecidableEq τ] {xs : Array (Option Bool)}
    (L : Bool ↪ τ) (c : Cfg τ (Option Bool) Unit xs) (q : ℕ) :
    Triple ((Program.onWork L localCopy).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 2 + q)
      (fun a s b ↦ a = c.workSymbols (L true) ∧
        s.workSymbols (L false) = a ∧
        s.workTapes (L true) = c.workTapes (L true) ∧
        s.workPos = c.workPos ∧ s.inputPos = c.inputPos ∧ s.output = c.output ∧
        (∀ j, j ∉ Set.range L → s.workTapes j = c.workTapes j) ∧ b = q) () := by
  have h := Program.spec_onWork L (localCopy_spec (c.restrictWorkAlong L) q) c
  constructor
  rintro s b ⟨hs, hb⟩
  subst s
  apply h.entails_wp_of_post ?_ c b ⟨rfl, rfl, hb⟩
  rintro a s b ⟨t, ⟨ha, hw, ht, hp, hi, ho, hq⟩, rfl⟩
  refine ⟨ha, ?_, ?_, ?_, hi, ho, ?_, hq⟩
  · simpa [Cfg.workSymbols, Cfg.replaceWorkAlong] using hw
  · simpa [Cfg.replaceWorkAlong, Cfg.restrictWorkAlong] using ht
  · simp [Cfg.replaceWorkAlong, hp, Cfg.restrictWorkAlong]
  · intro j hj
    exact L.replace_of_not_mem _ _ hj

end ProgramTapesTest
