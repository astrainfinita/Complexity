/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Program.WP

open Complexity

namespace ProgramBudgetTest

abbrev Code := Program Unit Unit Unit (fun _ : Unit ↦ Unit)

def model : Program.Semantics Unit Unit Unit (fun _ : Unit ↦ Unit) Unit where
  eval _ _ := ((), ())
  observe _ := ()
  act _ s := s

-- A successful primitive cannot be verified with a zero time budget.
example (Q : Unit → Unit → ℕ → Prop) :
    ¬(Program.perform ()).Total model Q () 0 := by
  rintro ⟨n, a, t, hn, h, _⟩
  have : n = 0 := by omega
  subst n
  cases h

-- The body does no work, but each iteration still takes one real control step.
def spin : Code (Fin 1) :=
  Program.loop () (fun i : Fin 1 ↦ pure (Sum.inl i)) 0

theorem spin_no_exec (n : ℕ) (s t : Unit) (a : Fin 1) :
    ¬spin.Exec model s n a t := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    intro h
    simp only [spin, Program.loop] at h
    cases h with
    | loop_done a i body k hb hk => cases hb
    | loop_next a i body k hb hk =>
      cases hb
      exact ih _ (Nat.lt_succ_self _) s (by
        simpa only [spin, Program.loop, Nat.zero_add, model] using hk)

-- Total WP rejects the nonterminating program at every finite budget.
example (Q : Fin 1 → Unit → ℕ → Prop) (b : ℕ) : ¬spin.Total model Q () b := by
  rintro ⟨n, a, t, _, h, _⟩
  exact spin_no_exec n () t a h

-- Infinite return types are allowed, but their labels are not written to a tape.
def label : Code (List ℕ) := pure [1, 2, 3]

example : Finite (label.State ⊕ label.Exit) := inferInstance

end ProgramBudgetTest
