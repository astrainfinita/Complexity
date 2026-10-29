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

abbrev Code := Program Unit Unit Unit (fun _ : Unit ↦ Unit)

def model : Program.Semantics Unit Unit Unit (fun _ : Unit ↦ Unit) Unit where
  eval _ _ := ((), ())
  observe _ := ()
  act _ s := s

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

theorem twice_exec : twice.Exec model () 2 () () := by
  obtain ⟨n, a, s, hn, he, hb⟩ := Program.exec_of_spec twice_spec rfl
  have h : n = 2 := by omega
  subst n
  cases a
  cases s
  exact he

-- Carrying a finite value does not make an endlessly continuing loop terminate.
def spin : Code Unit :=
  Program.loopOn () (fun b : Bool ↦ pure (Sum.inl b)) false

theorem spin_no_exec (n : ℕ) (s t : Unit) (a : Unit) :
    ¬spin.Exec model s n a t := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    intro h
    simp only [spin, Program.loopOn] at h
    cases h with
    | loop_done a i body k hb hk =>
      simp only [Program.loopOnBody] at hb
      cases hb
    | loop_next a i body k hb hk =>
      simp only [Program.loopOnBody] at hb
      cases hb
      exact ih _ (Nat.lt_succ_self _) s (by
        simpa only [spin, Program.loopOn, Equiv.apply_symm_apply, Nat.zero_add, model] using hk)

example (Q : Unit → Unit → ℕ → Prop) (b : ℕ) : ¬spin.Total model Q () b := by
  rintro ⟨n, a, t, _, h, _⟩
  exact spin_no_exec n () t a h

end ProgramLoopTest
