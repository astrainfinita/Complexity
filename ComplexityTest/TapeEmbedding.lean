/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.RedirectInput
import Complexity.Models.TuringMachine.RedirectOutput
meta import Complexity.Data.Embedding
meta import Complexity.Models.TuringMachine.Tapes
meta import Complexity.Models.TuringMachine.RedirectInput
meta import Complexity.Models.TuringMachine.RedirectOutput
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Transition
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory

open Complexity Complexity.TM

namespace TapeEmbeddingTest

-- Reverse the source order and leave gaps on both sides of its tapes.
def permuted : Fin 2 ↪ Fin 5 where
  toFun i := if i = 0 then 3 else 1
  inj' := by decide

-- The same injection allocates both work tapes and the separate I/O buffer.
def routed : (Fin 2 ⊕ Unit) ↪ Fin 5 where
  toFun := Sum.elim permuted (fun _ ↦ 0)
  inj' := by decide

-- Moving the entire five-tape bank one position right supplies a second layout.
def shifted : Fin 5 ↪ Fin 6 where
  toFun i := ⟨i.val + 1, by omega⟩
  inj' := by decide

def composed : Fin 2 ↪ Fin 6 := permuted.trans shifted

example : composed 0 = 4 ∧ composed 1 = 2 := by decide
example : 0 ∉ Set.range composed ∧ 1 ∉ Set.range composed := by decide

-- Replacement composition retains data outside both the source bank and the outer bank.
example (source : Fin 2 → ℕ) (target : Fin 6 → ℕ) :
    shifted.replace (permuted.replace source (target ∘ shifted)) target =
      composed.replace source target := permuted.replace_comp shifted source target

abbrev Symbol := Option Bool

def machine : TM Id (Fin 2) Symbol Bool where
  q₀ := false
  halt := id
  transition := fun _ (a, _) ↦ pure <|
    { inputMove := 1
      work := fun j ↦ if j = 0 then (some (some true), 1) else (some (some false), -1)
      output := some a
      state := true }

def caller (k : ℕ) : Cfg (Fin k) Symbol Bool #[some true] :=
  { (rawExecution (κ := Fin k) [some true]).init false with
    workTapes := fun _ ↦ (∅ : IntMemory Symbol).set 5 (some false)
    workPos := fun _ ↦ 5
    output := #[some false] }

def outputStart := RedirectOutput.cfgAlong routed ((machine.initInput (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool [some true].toArray) [some true])) (caller 5)

def outputEnd := (RedirectOutput.compilerAlong routed machine).runFrom outputStart 1

-- The source tapes move to 3 and 1; tape 0 is the output buffer; tape 2 is untouched.
#guard outputEnd.state
#guard (outputEnd.workTapes 3)[(0 : ℤ)] == some true
#guard (outputEnd.workTapes 1)[(0 : ℤ)] == some false
#guard outputEnd.workPos 3 == 1 && outputEnd.workPos 1 == -1
#guard (outputEnd.workTapes 0)[(0 : ℤ)] == some true && outputEnd.workPos 0 == 1
#guard (outputEnd.workTapes 2)[(5 : ℤ)] == some false && outputEnd.workPos 2 == 5
#guard outputEnd.output == #[some false]

example (n : ℕ) :
    (RedirectOutput.compilerAlong routed machine).runFrom outputStart n =
      RedirectOutput.cfgAlong routed (machine.run (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool [some true].toArray) [some true] n) (caller 5) :=
  RedirectOutput.runFrom_cfgAlong routed machine _ _ n

def composedEnd := (RedirectOutput.compilerAlong (routed.trans shifted) machine).runFrom
  (RedirectOutput.cfgAlong (routed.trans shifted) ((machine.initInput (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool [some true].toArray) [some true])) (caller 6)) 1

-- Composition maps 3/1 to 4/2 and the output buffer to 1; the new tape 0 remains intact.
#guard (composedEnd.workTapes 4)[(0 : ℤ)] == some true
#guard (composedEnd.workTapes 2)[(0 : ℤ)] == some false
#guard (composedEnd.workTapes 1)[(0 : ℤ)] == some true && composedEnd.workPos 1 == 1
#guard (composedEnd.workTapes 0)[(5 : ℤ)] == some false && composedEnd.workPos 0 == 5

example (a : Action (Fin 2) Symbol Bool) :
    (a.liftWorkAlong permuted).liftWorkAlong shifted = a.liftWorkAlong composed :=
  a.liftWorkAlong_comp permuted shifted

def inputStart := RedirectInput.cfgAlong routed #[true] (caller 5)
  ((machine.initInput (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool ([true].map some).toArray) ([true].map some))) false

def inputEnd := (RedirectInput.compilerAlong routed machine).runFrom inputStart 1

-- Input is read from tape 0; source writes still target 3/1, and the external input stays put.
#guard inputEnd.output == #[some true]
#guard inputEnd.inputPos.val == (caller 5).inputPos.val
#guard (inputEnd.workTapes 0)[(0 : ℤ)] == some true && inputEnd.workPos 0 == 1
#guard (inputEnd.workTapes 3)[(0 : ℤ)] == some true
#guard (inputEnd.workTapes 1)[(0 : ℤ)] == some false
#guard (inputEnd.workTapes 2)[(5 : ℤ)] == some false && inputEnd.workPos 2 == 5

example (n : ℕ) : ∃ flag,
    RedirectInput.Boundary (machine.run (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool ([true].map some).toArray) ([true].map some) n).inputPos flag ∧
      (RedirectInput.compilerAlong routed machine).runFrom inputStart n =
        RedirectInput.cfgAlong routed #[true] (caller 5)
          (machine.run (Input := List Symbol) (Config := Cfg (Fin 2) Symbol Bool ([true].map some).toArray) ([true].map some) n) flag :=
  RedirectInput.runFrom_cfgAlong routed machine #[true] (caller 5)
    _ false (by intro _; rfl) n

-- Sum indices give a named spare tape without any numeric embedding arithmetic.
def taggedMachine : TM Id Bool Symbol Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <|
    { inputMove := 0
      work b := (some (some b), if b then 1 else -1)
      output := some (some true)
      state := true }

def taggedEnd :=
  (RedirectOutput.compilerAlong (Function.Embedding.refl _) taggedMachine).runFrom
    (RedirectOutput.cfgAlong (Function.Embedding.refl _)
      ((taggedMachine.initInput (Input := List Symbol) (Config := Cfg Bool Symbol Bool #[]) [])) ((rawExecution (κ := Bool ⊕ Unit) (Γ := Symbol) []).init false)) 1

#guard (taggedEnd.workTapes (.inl false))[(0 : ℤ)] == some false
#guard (taggedEnd.workTapes (.inl true))[(0 : ℤ)] == some true
#guard taggedEnd.workPos (.inl false) == -1 && taggedEnd.workPos (.inl true) == 1
#guard (taggedEnd.workTapes (.inr ()))[(0 : ℤ)] == some true
#guard taggedEnd.workPos (.inr ()) == 1 && taggedEnd.output.isEmpty

example (n : ℕ) :
    (RedirectOutput.compilerAlong (Function.Embedding.refl _) taggedMachine).runFrom
        (RedirectOutput.cfgAlong (Function.Embedding.refl _)
          ((taggedMachine.initInput (Input := List Symbol) (Config := Cfg Bool Symbol Bool #[]) [])) ((rawExecution (κ := Bool ⊕ Unit) (Γ := Symbol) []).init false)) n =
      RedirectOutput.cfgAlong (Function.Embedding.refl _)
        (taggedMachine.run (Input := List Symbol) (Config := Cfg Bool Symbol Bool #[]) [] n) ((rawExecution (κ := Bool ⊕ Unit) (Γ := Symbol) []).init false) :=
  RedirectOutput.runFrom_cfgAlong (Function.Embedding.refl _) taggedMachine _ _ n

end TapeEmbeddingTest
