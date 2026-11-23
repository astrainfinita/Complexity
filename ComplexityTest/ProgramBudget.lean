/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Program.WP

open Complexity

namespace ProgramBudgetTest

abbrev Code := Program Id Unit Unit Unit (fun _ : Unit ↦ Unit)

def model : Program.Semantics Unit Unit Unit (fun _ : Unit ↦ Unit) Unit where
  eval _ _ := ((), ())
  observe _ := ()
  act _ s := s

-- A successful primitive cannot be verified with a zero time budget.
example (Q : Unit → Unit → ℕ → Prop) :
    ¬(Program.perform (F := Id) ()).ExecWithin model () 0 Q := fun h ↦
  Nat.lt_irrefl 0 (Program.Syntax.execWithinWith_step_iff.1 h).1

-- The body does no work, but each iteration still takes one real control step.
def spin : Code (Fin 1) :=
  Program.loop () (fun i : Fin 1 ↦ pure (Sum.inl i)) 0

-- Guards that the loop never returns: no execution within a budget reaches a return, at any
-- budget.
theorem spin_not_execWithin (s : Unit) (b : ℕ) (Q : Fin 1 → Unit → ℕ → Prop) :
    ¬spin.ExecWithin model s b Q := by
  induction b using Nat.strong_induction_on generalizing s with
  | h b ih =>
    intro h
    obtain ⟨hb, h⟩ := Program.Syntax.execWithinWith_loop_iff.1 h
    exact ih (b - 1) (by omega) s (Program.Syntax.execWithinWith_ret_iff.1 h)

-- Total WP rejects the nonterminating program at every finite budget.
example (Q : Fin 1 → Unit → ℕ → Prop) (b : ℕ) : ¬spin.ExecWithin model () b Q :=
  spin_not_execWithin () b Q

-- Infinite return types are allowed, but their labels are not written to a tape.
def label : Code (List ℕ) := pure [1, 2, 3]

example : Finite (label.State ⊕ label.Exit) := inferInstance

end ProgramBudgetTest
