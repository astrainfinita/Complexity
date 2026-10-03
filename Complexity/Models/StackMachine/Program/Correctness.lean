/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Program.Basic
public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Control.Program.Correctness

/-! # Resource bounds for native stack-program compilation -/

@[expose] public section

namespace Complexity.StackMachine.Program

open Std.WP

variable {κ Γ α : Type} {xs : Array Γ}

/-- Compiling the control graph preserves the action count and final storage. -/
theorem run_compile {p : StackMachine.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : Cfg κ Γ Unit xs} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result observe apply q s n a t) :
    ∃ e, p.result e = a ∧
      (compile p).runFrom (s.mapState (fun _ ↦ q)) n =
        t.mapState (fun _ ↦ Sum.inr e) := by
  induction h with
  | done e s => exact ⟨e, rfl, rfl⟩
  | step q s h ih => exact ih

/-- A total stack-program specification yields native computation and resource bounds. -/
theorem computesInTimeAndSpace [Fintype κ] (p : StackMachine.Program κ Γ α)
    {xs ys : List Γ} {t : ℕ}
    (h : Triple (p.verify (semantics xs.toArray))
      (fun c b ↦ c = (execution xs).init () ∧ t ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray) ()) :
    (compile p).ComputesInTimeAndSpace xs ys t (Fintype.card κ * t) := by
  obtain ⟨n, a, c, hn, he, ho⟩ := h.le_wp _ t ⟨rfl, le_rfl⟩
  obtain ⟨e, _, hr⟩ := run_compile (p := p) he.toControl
  change (compile p).run (Cfg κ Γ (p.State ⊕ p.Exit) xs.toArray) xs n = _ at hr
  apply ComputesInTimeAndSpace.of_run (n := n) (hn := hn)
  · change (compile p).halt _ = true
    rw [hr]
    rfl
  · rw [hr]
    exact ho

end Complexity.StackMachine.Program
