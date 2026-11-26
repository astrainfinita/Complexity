/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Program.Loop

set_option experimental.vcgen true

open Complexity Std.WP

namespace ProgramLoopTest

abbrev Code := Program Id Unit Unit Unit (fun _ : Unit ↦ Unit)

def model : Program.Semantics Unit Unit Unit (fun _ : Unit ↦ Unit) Unit where
  eval _ _ := ((), ())
  observe _ := ()
  act _ s := s

-- A successful primitive cannot be verified with a zero time budget.
example (Q : Unit → Unit → ℕ → Prop) :
    ¬(Program.perform (F := Id) ()).ExecWithin model () 0 Q := fun h ↦
  Nat.lt_irrefl 0 (Program.Syntax.execWithinWith_step_iff.1 h).1

def body (b : Bool) : Code (Bool ⊕ Unit) :=
  if b then pure (.inr ()) else pure (.inl true)

-- Only the two loop dispatches cost time; neither body executes a primitive.
def twice : Code Unit := Program.loopOn () body false

example : Finite (twice.State ⊕ twice.Exit) := inferInstance

theorem twice_spec :
    Triple (twice.verify model) (fun _ b ↦ b = 2) (fun _ _ b ↦ b = 0) () := by
  unfold twice body
  vcgen invariants
  | inv1 => fun b _ n ↦ n = if b then 1 else 2
  all_goals simp_all [model]
  split <;> omega

-- Carrying a finite value does not make an endlessly continuing loop terminate.
def spin : Code Unit :=
  Program.loopOn () (fun b : Bool ↦ pure (Sum.inl b)) false

-- Guards that the loop never returns: from any carried value, no execution within a budget
-- reaches a return, at any budget.
theorem spin_not_execWithin (x : Bool) (s : Unit) (b : ℕ) (Q : Unit → Unit → ℕ → Prop) :
    ¬(Program.loopOn () (fun b : Bool ↦ pure (Sum.inl b)) x : Code Unit).ExecWithin
      model s b Q := by
  induction b using Nat.strong_induction_on generalizing x s with
  | h b ih =>
    intro h
    obtain ⟨hb, h⟩ := Program.Syntax.execWithinWith_loop_iff.1 h
    exact ih (b - 1) (by omega) _ s (Program.Syntax.execWithinWith_ret_iff.1 h)

example (Q : Unit → Unit → ℕ → Prop) (b : ℕ) : ¬spin.ExecWithin model () b Q :=
  spin_not_execWithin false () b Q

end ProgramLoopTest
