/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice.Basic
meta import Complexity.Control.BinaryChoice.Basic
import Complexity.Models.TuringMachine.Deterministic
meta import Complexity.Models.TuringMachine.Deterministic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Cost
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Data.IntMemory.Basic

open Complexity Complexity.TM
-- Symbols and states are ordinary inhabited types, without an Option wrapper.
inductive Γ where
  | blank | zero | one
  deriving Inhabited, DecidableEq, BEq, Repr

-- Copy input until a blank is read. The designated halting state is `true`.
def copyInput : TM Id (Fin 0) Γ Bool where
  q₀ := false
  halt := id
  transition := fun _ (a, _) ↦ pure <|
    { inputMove := .pos
      work := Fin.elim0
      output := if a == .blank then none else some a
      state := a == .blank }

#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [.one, .zero, .one].toArray) [.one, .zero, .one] 3).output = #[.one, .zero, .one]
#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [.one, .zero, .one].toArray) [.one, .zero, .one] 3).state = false
#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [.one, .zero, .one].toArray) [.one, .zero, .one] 4).state = true
#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [.one, .zero, .one].toArray) [.one, .zero, .one] 20).output = #[.one, .zero, .one]
#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [].toArray) [] 1).state = true
#guard (copyInput.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [].toArray) [] 1).output = #[]
#guard (copyInput.runHistory (Cfg (Fin 0) Γ Bool [.one, .zero].toArray) ([.one, .zero] : List Γ) 10).space = 0

-- Outward input moves clamp, including on an empty input.
#guard (Input.movePos (0 : Fin 5) .neg).val = 0
#guard (Input.movePos (4 : Fin 5) .pos).val = 4
#guard (Input.movePos (1 : Fin 2) .pos).val = 1
#guard (Input.movePos (1 : Fin 2) .neg).val = 0

-- All work tapes write at their old head positions, before their heads move.
def writeBoth : Action (Fin 2) Γ Bool where
  inputMove := .zero
  work i := if i = 0 then (some .one, .neg) else (some .zero, .pos)
  output := some .one
  state := true

def afterWrite : Cfg (Fin 2) Γ Bool #[] :=
  apply writeBoth ((rawExecution []).init false)

#guard (afterWrite.workTapes 0)[(0 : ℤ)] = .one
#guard (afterWrite.workTapes 1)[(0 : ℤ)] = .zero
#guard afterWrite.workPos 0 = -1
#guard afterWrite.workPos 1 = 1
#guard afterWrite.workSymbols 0 = .blank
#guard afterWrite.workSymbols 1 = .blank
#guard afterWrite.output = #[.one]
#guard afterWrite.state = true

-- Writing `default` erases a cell; omitting a write preserves its current contents.
def eraseFirst : Action (Fin 2) Γ Bool where
  inputMove := .zero
  work i := (if i = 0 then some default else none, .zero)
  output := none
  state := true

def afterErase : Cfg (Fin 2) Γ Bool #[] :=
  apply eraseFirst { afterWrite with workPos := fun _ ↦ 0 }

#guard (afterErase.workTapes 0)[(0 : ℤ)] = .blank
#guard (afterErase.workTapes 1)[(0 : ℤ)] = .zero

-- An action entering a halting state still writes and emits; later steps do nothing.
def haltAfterWrite : TM Id (Fin 2) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := pure writeBoth

#guard (haltAfterWrite.run (Input := List Γ) (Cfg (Fin 2) Γ Bool [].toArray) [] 10).output = #[.one]
#guard ((haltAfterWrite.run (Input := List Γ) (Cfg (Fin 2) Γ Bool [].toArray) [] 10).workTapes 0)[(0 : ℤ)] = .one
#guard (haltAfterWrite.runHistory (Cfg (Fin 2) Γ Bool #[]) ([] : List Γ) 0).space = 2
#guard (haltAfterWrite.runHistory (Cfg (Fin 2) Γ Bool #[]) ([] : List Γ) 1).space = 4
#guard (haltAfterWrite.runHistory (Cfg (Fin 2) Γ Bool #[]) ([] : List Γ) 10).space = 4

-- Space counts visited blank cells, even when a machine never writes or halts.
def walkLeft : TM Id (Fin 1) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <|
    { inputMove := .zero
      work := fun _ ↦ (none, .neg)
      output := none
      state := false }

#guard (walkLeft.runHistory (Cfg (Fin 1) Γ Bool #[]) ([] : List Γ) 5).space = 6
#guard ((walkLeft.run (Input := List Γ) (Cfg (Fin 1) Γ Bool [].toArray) [] 5).workTapes 0)[(-3 : ℤ)] = .blank

-- Distinct choices with equal successors retain their multiplicity in the Multiset monad.
def fork : TM BinaryChoice (Fin 0) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ :=
    let a : Action (Fin 0) Γ Bool := ⟨.zero, Fin.elim0, some .one, true⟩
    fun _ ↦ a

#guard (fork.runWith (Cfg (Fin 0) Γ Bool #[]) Multiset ([] : List Γ) 1).map (·.output) = ↑[#[Γ.one], #[Γ.one]]
#guard (fork.runWith (Cfg (Fin 0) Γ Bool #[]) Multiset ([] : List Γ) 5).map (·.output) = ↑[#[Γ.one], #[Γ.one]]

#guard (fork.runHistoryWith (Cfg (Fin 0) Γ Bool #[]) Multiset ([] : List Γ) 2).map (fun h ↦ h.space) = ↑[0, 0]

-- Failure of an effect is distinct from a halting state.
def abort : TM Option (Fin 0) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := none

#guard (abort.runWith (Cfg (Fin 0) Γ Bool #[]) Option ([] : List Γ) 1).isNone
#guard (abort.runWith (Cfg (Fin 0) Γ Bool #[]) Option ([] : List Γ) 0).isSome
#guard (abort.runFromWith Option { (abort.initInput (Input := List Γ) (Config := Cfg (Fin 0) Γ Bool [].toArray) []) with state := true } 10).isSome

-- Halting is allowed already at time zero, and the transition is never executed.
def alreadyHalted : TM Id (Fin 0) Γ Bool where
  q₀ := true
  halt := id
  transition _ _ := pure <| ⟨.zero, Fin.elim0, some .one, false⟩

#guard (alreadyHalted.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [].toArray) [] 0).state
#guard (alreadyHalted.run (Input := List Γ) (Cfg (Fin 0) Γ Bool [].toArray) [] 10).output = #[]

-- Each active step makes a fresh choice; both mixed histories must occur.
def twoChoices : TM BinaryChoice (Fin 0) Γ (Fin 3) where
  q₀ := 0
  halt q := q == 2
  transition q _ b :=
    { inputMove := 0, work := Fin.elim0
      output := some (if b = 0 then .zero else .one)
      state := if q = 0 then 1 else 2 }

#guard (twoChoices.runWith (Cfg (Fin 0) Γ (Fin 3) #[]) Multiset ([] : List Γ) 2).map (·.output) =
  ↑[#[Γ.zero, Γ.zero], #[Γ.zero, Γ.one], #[Γ.one, Γ.zero], #[Γ.one, Γ.one]]
#guard (twoChoices.runWith (Cfg (Fin 0) Γ (Fin 3) #[]) Multiset ([] : List Γ) 8).map (·.output) =
  (twoChoices.runWith (Cfg (Fin 0) Γ (Fin 3) #[]) Multiset ([] : List Γ) 2).map (·.output)
