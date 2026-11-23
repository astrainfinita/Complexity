/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Basic
public import Complexity.Control.Program.Correctness
public import Complexity.Control.Controller.RunHistory
public import Complexity.Models.TuringMachine.Deterministic

/-!
# Resource-preserving compilation of finite programs

One program transition is exactly one transition of its compiled machine. The history
maintained by the program semantics covers the machine's visited work cells, including
the initial positions. Thus a total program execution proves actual machine termination,
output correctness, and bounds in `ComputesWithin`.
-/

@[expose] public section

namespace Complexity.TM.Program

open Controller (History)

variable {κ : Type} {Γ α : Type} [Inhabited Γ] {xs : Array Γ}

/-- A source execution within the time budget proves output, time, and visited-cell space of the
compiled machine. -/
theorem computesWithin_of_execWithin [Fintype κ] (p : TM.Program Id κ Γ α) {ys : Array Γ}
    {t s : ℕ}
    (h : Program.Syntax.ExecWithin (⟨eval, observe, apply⟩ : Program.Semantics _ _ _ _ _)
      p (History.nil (Cfg.init κ xs.toList)) t (fun _ v _ ↦ v.last.output = ys ∧ v.space ≤ s)) :
    (compile p).ComputesWithin xs.toList ys.toList t s := by
  obtain ⟨e, v, hr, -, -, ho, hs⟩ := Program.Syntax.ExecWithin.runFrom_compile idle h
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact .of_halted t ((congrArg (compile p).halt hr.1).trans rfl)
    ((congrArg Cfg.output hl).trans ho)
    ((History.length_snd _).trans_le ((compile p).length_runHistory_le _ t))
    ((congrArg History.space hr.2).le.trans hs)

end Complexity.TM.Program
