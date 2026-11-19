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

/-- A source execution from standard input yields the same output after the same number
of transitions. This count is independent of the size-charged cost model. -/
theorem run_output [NeZero k] {p : TreeMachine.Program Id k α} {x y : Tree}
    {n : ℕ} {a : α} {c : Cfg k}
    (h : p.Exec semantics (Cfg.init k x) n a c) (ho : c.regs 0 = y) :
    (compile p).Halted ((compile p).run x n) ∧ ((compile p).run x n).2.regs 0 = y := by
  obtain ⟨e, _, hr⟩ := h.runFrom_compile .nop
  have hr' : (compile p).run x n = (.inr e, c) := hr
  rw [hr']
  exact ⟨rfl, ho⟩

end Complexity.TreeMachine.Program
