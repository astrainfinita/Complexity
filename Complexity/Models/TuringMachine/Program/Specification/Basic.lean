/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.WP
public import Complexity.Models.TuringMachine.Program.Basic

/-! # Verification rules independent of the semantic state -/

@[expose] public section

namespace Complexity.TM.Program

variable {κ : Type} {Γ S : Type}
  (e : Complexity.Program.Semantics (Γ × (κ → Γ)) (Action κ Γ Unit)
    (Op κ Γ) Op.Result S)

/-- Expose a work write as its one local action. -/
@[spec]
theorem verify_write [DecidableEq κ] (i : κ) (a : Γ) :
    (write i a).verify e =
      (act { idle (κ := κ) with work := fun j ↦ (if j = i then some a else none, 0) }).verify
        e := rfl

/-- Expose a work-head move as its one local action. -/
@[spec]
theorem verify_move [DecidableEq κ] (i : κ) (d : SignType) :
    (move i d).verify e =
      (act { idle (κ := κ) with work := fun j ↦ (none, if j = i then d else 0) }).verify
        e := rfl

/-- Expose an input-head move as its one local action. -/
@[spec]
theorem verify_moveInput (d : SignType) :
    (moveInput (κ := κ) d).verify e =
      (act { idle (κ := κ) with inputMove := d }).verify e := rfl

/-- Expose output as the local action which appends its symbol. -/
@[spec]
theorem verify_emit (a : Γ) :
    (emit (κ := κ) a).verify e =
      (act { idle (κ := κ) with output := some a }).verify e := rfl

end Complexity.TM.Program
