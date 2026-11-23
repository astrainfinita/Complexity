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

variable {F : Type → Type} {κ : Type} {Γ S : Type} {m : Type → Type} [Monad m] {Q : MonadQuant m}
  (e : Program.Semantics (Γ × (κ → Γ)) (Action κ Γ)
    (Op κ Γ) Op.Result S)

/-- Expose a work write as its one local action. -/
@[spec]
theorem verifyWith_write [DecidableEq κ] (i : κ) (a : Γ) :
    (write (F := F) i a).verifyWith m Q e =
      (act { idle (κ := κ) with work := fun j ↦ (if j = i then some a else none, 0) }).verifyWith
        m Q e := rfl

/-- Expose a work-head move as its one local action. -/
@[spec]
theorem verifyWith_move [DecidableEq κ] (i : κ) (d : SignType) :
    (move (F := F) i d).verifyWith m Q e =
      (act { idle (κ := κ) with work := fun j ↦ (none, if j = i then d else 0) }).verifyWith
        m Q e := rfl

/-- Expose an input-head move as its one local action. -/
@[spec]
theorem verifyWith_moveInput (d : SignType) :
    (moveInput (F := F) d).verifyWith m Q e =
      (act { idle with inputMove := d }).verifyWith m Q e := rfl

/-- Expose output as the local action which appends its symbol. -/
@[spec]
theorem verifyWith_emit (a : Γ) :
    (emit (F := F) a).verifyWith m Q e =
      (act { idle with output := some a }).verifyWith m Q e := rfl

end Complexity.TM.Program
