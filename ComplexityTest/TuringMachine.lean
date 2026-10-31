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
    (a == .blank,
      { inputMove := .pos
        work := Fin.elim0
        output := if a == .blank then none else some a })

#guard (copyInput.run (Input := List Γ) [.one, .zero, .one] 3).2.output = #[.one, .zero, .one]
#guard (copyInput.run (Input := List Γ) [.one, .zero, .one] 3).1 = false
#guard (copyInput.run (Input := List Γ) [.one, .zero, .one] 4).1 = true
#guard (copyInput.run (Input := List Γ) [.one, .zero, .one] 20).2.output = #[.one, .zero, .one]
#guard (copyInput.run (Input := List Γ) [] 1).1 = true
#guard (copyInput.run (Input := List Γ) [] 1).2.output = #[]
#guard (copyInput.runHistory ([.one, .zero] : List Γ) 10).snd.space = 0

-- Outward input moves clamp, including on an empty input.
#guard (Input.movePos (0 : Fin 5) .neg).val = 0
#guard (Input.movePos (4 : Fin 5) .pos).val = 4
#guard (Input.movePos (1 : Fin 2) .pos).val = 1
#guard (Input.movePos (1 : Fin 2) .neg).val = 0

-- All work tapes write at their old head positions, before their heads move.
def writeBoth : Action (Fin 2) Γ where
  inputMove := .zero
  work i := if i = 0 then (some .one, .neg) else (some .zero, .pos)
  output := some .one

def afterWrite : Bool × Cfg (Fin 2) Γ #[] :=
  apply (true, writeBoth) (false, Cfg.init (Fin 2) [])

#guard (afterWrite.2.workTapes 0)[(0 : ℤ)] = .one
#guard (afterWrite.2.workTapes 1)[(0 : ℤ)] = .zero
#guard afterWrite.2.workPos 0 = -1
#guard afterWrite.2.workPos 1 = 1
#guard afterWrite.2.workSymbols 0 = .blank
#guard afterWrite.2.workSymbols 1 = .blank
#guard afterWrite.2.output = #[.one]
#guard afterWrite.1 = true

-- Writing `default` erases a cell; omitting a write preserves its current contents.
def eraseFirst : Action (Fin 2) Γ where
  inputMove := .zero
  work i := (if i = 0 then some default else none, .zero)
  output := none

def afterErase : Cfg (Fin 2) Γ #[] :=
  apply eraseFirst { afterWrite.2 with workPos := fun _ ↦ 0 }

#guard (afterErase.workTapes 0)[(0 : ℤ)] = .blank
#guard (afterErase.workTapes 1)[(0 : ℤ)] = .zero

-- An action entering a halting state still writes and emits; later steps do nothing.
def haltAfterWrite : TM Id (Fin 2) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := pure (true, writeBoth)

#guard (haltAfterWrite.run (Input := List Γ) [] 10).2.output = #[.one]
#guard ((haltAfterWrite.run (Input := List Γ) [] 10).2.workTapes 0)[(0 : ℤ)] = .one
#guard (haltAfterWrite.runHistory ([] : List Γ) 0).snd.space = 2
#guard (haltAfterWrite.runHistory ([] : List Γ) 1).snd.space = 4
#guard (haltAfterWrite.runHistory ([] : List Γ) 10).snd.space = 4

-- Space counts visited blank cells, even when a machine never writes or halts.
def walkLeft : TM Id (Fin 1) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <|
    (false,
      { inputMove := .zero
        work := fun _ ↦ (none, .neg)
        output := none })

#guard (walkLeft.runHistory ([] : List Γ) 5).snd.space = 6
#guard ((walkLeft.run (Input := List Γ) [] 5).2.workTapes 0)[(-3 : ℤ)] = .blank

-- Distinct choices with equal successors retain their multiplicity in the Multiset monad.
def fork : TM BinaryChoice (Fin 0) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ :=
    let a : Bool × Action (Fin 0) Γ := (true, ⟨.zero, Fin.elim0, some .one⟩)
    fun _ ↦ a

#guard (fork.runWith Multiset ([] : List Γ) 1).map (·.2.output) = ↑[#[Γ.one], #[Γ.one]]
#guard (fork.runWith Multiset ([] : List Γ) 5).map (·.2.output) = ↑[#[Γ.one], #[Γ.one]]

#guard (fork.runHistoryWith Multiset ([] : List Γ) 2).map
  (fun h ↦ h.snd.space) = ↑[0, 0]

-- Failure of an effect is distinct from a halting state.
def abort : TM Option (Fin 0) Γ Bool where
  q₀ := false
  halt := id
  transition _ _ := none

#guard (abort.runWith Option ([] : List Γ) 1).isNone
#guard (abort.runWith Option ([] : List Γ) 0).isSome
#guard (abort.runFromWith Option (true, (abort.init ([] : List Γ)).2) 10).isSome

-- Halting is allowed already at time zero, and the transition is never executed.
def alreadyHalted : TM Id (Fin 0) Γ Bool where
  q₀ := true
  halt := id
  transition _ _ := pure <| (false, ⟨.zero, Fin.elim0, some .one⟩)

#guard (alreadyHalted.run (Input := List Γ) [] 0).1
#guard (alreadyHalted.run (Input := List Γ) [] 10).2.output = #[]

-- Each active step makes a fresh choice; both mixed histories must occur.
def twoChoices : TM BinaryChoice (Fin 0) Γ (Fin 3) where
  q₀ := 0
  halt q := q == 2
  transition q _ b :=
    (if q = 0 then 1 else 2,
      { inputMove := 0, work := Fin.elim0
        output := some (if b = 0 then .zero else .one) })

#guard (twoChoices.runWith Multiset ([] : List Γ) 2).map (·.2.output) =
  ↑[#[Γ.zero, Γ.zero], #[Γ.zero, Γ.one], #[Γ.one, Γ.zero], #[Γ.one, Γ.one]]
#guard (twoChoices.runWith Multiset ([] : List Γ) 8).map (·.2.output) =
  (twoChoices.runWith Multiset ([] : List Γ) 2).map (·.2.output)
