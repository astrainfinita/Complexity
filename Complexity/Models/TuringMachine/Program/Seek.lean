/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Traverse
public import Complexity.Models.TuringMachine.Program.Basic

/-!
# Seeking a work-tape delimiter

Each continuing iteration reads a symbol and moves one cell. The stopping iteration only
reads. Including loop dispatch, seeking across `n` cells costs exactly `3 * n + 2` steps.
The same rule applies to configurations and to states carrying visitation history.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {κ : Type} [DecidableEq κ] {Γ S : Type} [FinEnum Γ]

/-- Read one cell, stopping at the selected delimiter or moving in the selected direction. -/
def seekBody (j : κ) (d : SignType) (stop : Γ → Prop) [DecidablePred stop] :
    TM.Program κ Γ Bool := do
  let a ← read j
  if stop a then
    pure true
  else
    move j d
    pure false

/-- Seek the first symbol satisfying `stop`, leaving the head on that symbol. -/
def seek (j : κ) (d : SignType) (stop : Γ → Prop) [DecidablePred stop] :
    TM.Program κ Γ Unit := repeatUntil (seekBody j d stop)

variable (e : Program.Semantics (Γ × (κ → Γ)) (Action κ Γ Unit)
  (Op κ Γ) Op.Result S) (he : e.eval = eval)

include he

/-- A stopping read takes one step and preserves a state on which idle is the identity. -/
theorem exec_seekBody_stop (j : κ) (d : SignType) (stop : Γ → Prop)
    [DecidablePred stop] (s : S) (hi : e.act idle s = s)
    (hs : stop ((e.observe s).2 j)) :
    (seekBody j d stop).Exec e s 1 true s := by
  have hr : (read j).Exec e s 1 ((e.observe s).2 j) s := by
    simpa only [read, he, eval, hi] using
      Program.Exec.perform e (Op.read (Γ := Γ) inferInstance j) s
  unfold seekBody
  apply Program.Exec.bind (m := 1) (n := 0) hr
  simpa only [ite_eq_left hs, Pure.pure] using Program.Exec.pure e true s

/-- A continuing iteration takes one read and one move, independently of ghost fields. -/
theorem exec_seekBody_move (j : κ) (d : SignType) (stop : Γ → Prop)
    [DecidablePred stop] (s : S) (hi : e.act idle s = s)
    (hs : ¬stop ((e.observe s).2 j)) :
    (seekBody j d stop).Exec e s 2 false (e.act (moveAction j d) s) := by
  have hr : (read j).Exec e s 1 ((e.observe s).2 j) s := by
    simpa only [read, he, eval, hi] using
      Program.Exec.perform e (Op.read (Γ := Γ) inferInstance j) s
  have hm : (move j d).Exec e s 1 () (e.act (moveAction j d) s) := by
    simpa only [move_eq_act, act, he, eval] using
      Program.Exec.perform e (Op.act (moveAction j d)) s
  unfold seekBody
  apply Program.Exec.bind (m := 1) (n := 1) hr
  simp only [ite_eq_right hs]
  exact hm.bind (f := fun _ ↦ Program.pure false)
    (Program.Exec.pure e false _)

/-- A counted seek only needs the delimiter test and preservation by its head movement.
The interpretation may include any ghost state, provided idle preserves the invariant. -/
theorem spec_seek (j : κ) (d : SignType) (stop : Γ → Prop) [DecidablePred stop]
    (I : ℕ → S → Prop) (n q : ℕ)
    (hi : ∀ r ≤ n, ∀ s, I r s → e.act idle s = s)
    (hm : ∀ r < n, ∀ s, I r s →
      ¬stop ((e.observe s).2 j) ∧ I (r + 1) (e.act (moveAction j d) s))
    (hs : ∀ s, I n s → stop ((e.observe s).2 j)) :
    Triple ((seek j d stop).verify e)
      (fun s b ↦ I 0 s ∧ b = 3 * n + 2 + q)
      (fun _ s b ↦ I n s ∧ b = q) () := by
  apply Program.spec_repeatUntilWith_count idle (seekBody j d stop)
    e I (I n) n 2 1 q hi
  · intro r hr v
    constructor
    rintro s b ⟨hI, rfl⟩
    obtain ⟨hstop, hmove⟩ := hm r hr s hI
    exact ⟨2, false, e.act (moveAction j d) s, by omega,
      exec_seekBody_move e he j d stop s (hi r hr.le s hI) hstop,
      rfl, hmove, by omega⟩
  · intro v
    constructor
    rintro s b ⟨hI, rfl⟩
    exact ⟨1, true, s, by omega,
      exec_seekBody_stop e he j d stop s (hi n le_rfl s hI) (hs s hI),
      rfl, hI, by omega⟩

end Complexity.TM.Program
