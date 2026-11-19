/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Call
import all Init.Data.List.Scan.Basic

meta import Complexity.Control.Controller.History.Basic
meta import Complexity.Models.TuringMachine.History
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Transition.Basic
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory.Basic
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Cost
meta import Mathlib.Order.Interval.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Program.Call

set_option experimental.vcgen true

open Complexity (TM IntMemory Controller Program)
open Complexity.TM Std.WP
open Complexity.Controller (History)

namespace ProgramCallTest

def machine : TM Id (Fin 1) Bool Bool where
  q₀ := false
  halt := id
  transition _ _ := pure
    (true, { inputMove := 0, work := fun _ ↦ (some true, 1), output := some false })

private theorem machine_run_one :
    machine.runFrom (machine.q₀, Cfg.init (Fin 1) ([] : List Bool)) 1 =
      (true,
        { inputPos := 1, workTapes := fun _ ↦ (∅ : IntMemory Bool).set 0 true,
          workPos := fun _ ↦ 1, output := #[false] }) := rfl

-- A returned machine state and its stored result are usable by the continuation.
def demo : TM.Program Id (Fin 1) Bool Bool := do
  let q ← Program.call machine
  Program.move 0 (-1)
  let a ← Program.read 0
  Program.emit a
  pure (q && a)

-- An initially halted call performs no action, even when the enclosing machine is padded.
example : (Program.compile (Program.callFrom machine true)).halt
    (Program.compile (Program.callFrom machine true)).q₀ = true :=
  Program.halt_start_callFrom machine true
example :
    ((Program.compile (Program.callFrom machine true)).run (Input := List Bool) [] 3).2.output =
      #[] := by
  rw [Controller.run, Controller.runFrom_of_halted _ _
    (by exact Program.halt_start_callFrom machine true)]
  rfl
example : ((Program.compile (Program.call machine)).run (Input := List Bool) [] 1).2.output =
    #[false] := by
  rw [Controller.run_succ, Controller.run_zero, TM.step_eq]
  simp [Program.call, Program.compile, Program.Syntax.compile, Program.callFrom,
    Program.callBlock, Program.blockRoute, Program.callControl, Program.Syntax.toControl,
    Program.Syntax.callLabel, Program.Syntax.callCont,
    machine]
  rfl

#guard ((Program.compile demo).run (Input := List Bool) [] 4).2.output == #[false, true]
#guard (((Program.compile demo).run (Input := List Bool) [] 4).2.workTapes 0)[(0 : ℤ)]

theorem demo_spec : Triple (demo.verify (Program.cfgSemantics #[]))
    (fun c b ↦ c = Cfg.init (Fin 1) [] ∧ b = 4)
    (fun a c _ ↦ a = true ∧ c.output = #[false, true] ∧ c.workPos 0 = 0) () := by
  have hc := Program.cfg_spec_call machine (Cfg.init (Fin 1) ([] : List Bool)) 1 3 (by rfl)
  unfold demo
  vcgen [hc]
  all_goals simp_all only [machine_run_one]
  all_goals simp_all [machine, Program.idle, Cfg.workSymbols]
  all_goals omega

-- Earlier visits remain part of the caller's history; the current head is still at zero.
private def moveHistory (d : SignType)
    (s : History (Cfg (Fin 1) Bool #[]) (Action (Fin 1) Bool)) :=
  s.snoc { Program.idle (κ := Fin 1) with work := fun _ ↦ (none, d) }

def start : History (Cfg (Fin 1) Bool #[]) (Action (Fin 1) Bool) :=
  (moveHistory (-1))^[4] ((moveHistory 1)^[7]
    ((moveHistory (-1))^[3] (History.nil (Cfg.init (Fin 1) []))))

private def historyDemo : History (Cfg (Fin 1) Bool #[]) (Action (Fin 1) Bool) :=
  (demo.compile.runFrom (demo.compile.q₀, start) 10).2

#guard historyDemo.visited 0 = start.visited 0
#guard historyDemo.space = 8
#guard historyDemo.last.workPos 0 = 0
#guard historyDemo.last.output = #[false, true]

end ProgramCallTest
