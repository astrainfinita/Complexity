/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Call.Resources

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Transition
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Cost
meta import Mathlib.Order.Interval.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Tapes
meta import Complexity.Models.TuringMachine.Program.Call

set_option experimental.vcgen true

open Complexity (TM IntMemory Controller Program)
open Complexity.TM Std.WP

namespace ProgramCallTest

def machine : TM Id (Fin 1) Bool Bool where
  q₀ := false
  halt := id
  transition _ _ := pure
    { inputMove := 0, work := fun _ ↦ (some true, 1), output := some false, state := true }

private theorem machine_run_one :
    machine.runFrom (machine.initInput (Config := Cfg (Fin 1) Bool Bool #[]) ([] : List Bool)) 1 =
      { state := true, inputPos := 1, workTapes := fun _ ↦ (∅ : IntMemory Bool).set 0 true,
        workPos := fun _ ↦ 1, output := #[false] } := rfl

-- A returned machine state and its stored result are usable by the continuation.
def demo : TM.Program (Fin 1) Bool Bool := do
  let q ← Program.call machine
  Program.move 0 (-1)
  let a ← Program.read 0
  Program.emit a
  pure (q && a)

-- An initially halted call performs no action, even when the enclosing machine is padded.
example : (Program.compile (Program.callFrom machine true)).halt
    (Program.compile (Program.callFrom machine true)).q₀ = true :=
  Program.halt_start_callFrom machine true
example : ((Program.compile (Program.callFrom machine true)).run (Input := List Bool) (Cfg (Fin 1) Bool ((Program.callFrom machine true).State ⊕ (Program.callFrom machine true).Exit) [].toArray) [] 3).output = #[] := by
  rw [Controller.run, Controller.runFrom_of_halted _ _
    (by exact Program.halt_start_callFrom machine true)]
  rfl
example : ((Program.compile (Program.call machine)).run (Input := List Bool) (Cfg (Fin 1) Bool ((Program.call machine).State ⊕ (Program.call machine).Exit) [].toArray) [] 1).output = #[false] := by
  change ((Program.compile (Program.call machine)).step
    ((Program.compile (Program.call machine)).initInput (Input := List Bool) (Config := Cfg (Fin 1) Bool ((Program.call machine).State ⊕ (Program.call machine).Exit) [].toArray) [])).output = _
  rw [TM.step_eq]
  simp [Program.call, Program.compile, Program.callFrom, Program.callBlock, Program.blockRoute,
    Program.callControl, Program.Syntax.toControl,
    Program.Syntax.callLabel, Program.Syntax.callCont,
    machine, Action.mapState]
  rfl

#guard ((Program.compile demo).run (Input := List Bool) (Cfg (Fin 1) Bool ((demo).State ⊕ (demo).Exit) [].toArray) [] 4).output == #[false, true]
#guard (((Program.compile demo).run (Input := List Bool) (Cfg (Fin 1) Bool ((demo).State ⊕ (demo).Exit) [].toArray) [] 4).workTapes 0)[(0 : ℤ)]

theorem demo_spec : Triple (demo.verify (Program.cfgSemantics #[]))
    (fun c b ↦ c = (rawExecution []).init () ∧ b = 4)
    (fun a c _ ↦ a = true ∧ c.output = #[false, true] ∧ c.workPos 0 = 0) () := by
  have hc := Program.cfg_spec_call machine ((machine.initInput (Input := List Bool) (Config := Cfg (Fin 1) Bool Bool [].toArray) [])) 1 3 rfl (by rfl)
  unfold demo
  vcgen [hc]
  all_goals simp_all only [machine_run_one]
  all_goals simp_all [machine, Cfg.mapState,
    Program.idle, Cfg.workSymbols]
  all_goals omega

-- Earlier visits remain part of the caller's history; the current head is still at zero.
def start : TrackedCfg (Fin 1) Bool Unit #[] where
  cfg := (rawExecution []).init ()
  visited := fun _ ↦ ⟨(-3, 4), by decide⟩
  head_mem := by intro i; change (-3 : ℤ) ≤ 0 ∧ 0 ≤ 4; decide

private def trackedDemo : TrackedCfg (Fin 1) Bool (demo.State ⊕ demo.Exit) #[] :=
  demo.compile.runFrom (start.mapState (fun _ ↦ demo.compile.q₀)) 10

#guard trackedDemo.visited 0 = start.visited 0
#guard trackedDemo.space = 8
#guard trackedDemo.cfg.workPos 0 = 0
#guard trackedDemo.cfg.output = #[false, true]

theorem demo_visited_le_spec : Triple (demo.verify (Program.semantics #[]))
    (fun s b ↦ s = start ∧ b = 4)
    (fun a s _ ↦ a = true ∧ s.cfg.output = #[false, true] ∧ s.cfg.workPos 0 = 0 ∧
      s.visited ≤ (fun _ ↦ ⟨(-3, 4), by decide⟩)) () := by
  have hc := Program.spec_call_visited_le machine ((machine.initInput (Input := List Bool) (Config := Cfg (Fin 1) Bool Bool [].toArray) [])) 1 3
    (fun _ ↦ ⟨(-3, 4), by decide⟩) rfl (by rfl) (by decide)
  unfold demo
  vcgen [hc]
  all_goals simp_all only [machine_run_one]
  all_goals simp_all [machine, Cfg.mapState,
    Program.idle, Cfg.workSymbols, start,
    Pi.le_def, NonemptyInterval.le_def, Fin.eq_zero]
  all_goals omega

end ProgramCallTest
