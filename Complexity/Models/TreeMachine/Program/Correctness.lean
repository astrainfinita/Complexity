/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Basic
public import Complexity.Control.Program.Correctness

/-! # Native execution of tree-register programs -/

@[expose] public section

namespace Complexity.TreeMachine.Program

variable {k : ℕ} {α : Type}

/-- Compiling the control graph preserves the action count and every register. -/
theorem run_compile {p : TreeMachine.Program k α} {q : p.State ⊕ p.Exit}
    {ρ σ : Fin k → Tree} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result semantics.observe semantics.act
      q ρ n a σ) :
    ∃ e, p.result e = a ∧ (compile p).runFrom (Cfg.mk q ρ) n = Cfg.mk (.inr e) σ := by
  induction h with
  | done e ρ => exact ⟨e, rfl, rfl⟩
  | step q ρ h ih => exact ih

/-- A source execution from standard input yields the same output after the same number
of transitions. This count is independent of the destination-size cost model. -/
theorem run_output [NeZero k] {p : TreeMachine.Program k α} {x y : Tree}
    {n : ℕ} {a : α} {ρ : Fin k → Tree}
    (h : p.Exec semantics (input 0 x) n a ρ) (ho : ρ 0 = y) :
    (compile p).Halted ((compile p).run (Cfg k (p.State ⊕ p.Exit)) x n) ∧
      ((compile p).run (Cfg k (p.State ⊕ p.Exit)) x n).regs 0 = y := by
  obtain ⟨e, _, hr⟩ := run_compile h.toControl
  change (compile p).run (Cfg k (p.State ⊕ p.Exit)) x n = _ at hr
  constructor
  · change (compile p).halt _ = true
    rw [hr]
    rfl
  · rw [hr]
    exact ho

end Complexity.TreeMachine.Program
