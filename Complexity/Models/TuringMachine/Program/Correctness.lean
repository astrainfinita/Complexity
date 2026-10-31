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

/-- Running the compiled machine on a history records the program's history. One program
transition is one machine transition. -/
theorem run_compile {p : TM.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg κ Γ xs) (Action κ Γ)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result observe apply q s n a t) :
    ∃ e : p.Exit, p.result e = a ∧ (compile p).runFrom (q, s) n = (.inr e, t) := by
  induction h with
  | done e s => exact ⟨e, rfl, rfl⟩
  | step q s h ih => exact ih

/-- A source execution proves output, time, and visited-cell space of the compiled machine. -/
theorem computesWithin_of_exec [Fintype κ] (p : TM.Program κ Γ α) {ys : Array Γ}
    {n t s : ℕ} {a : α} {v : History (Cfg κ Γ xs) (Action κ Γ)}
    (h : Program.Syntax.Exec
      (⟨eval, observe, apply⟩ : Program.Semantics _ _ _ _ _)
      p (History.nil (Cfg.init κ xs.toList)) n a v)
    (hn : n ≤ t) (ho : v.last.output = ys) (hs : v.space ≤ s) :
    (compile p).ComputesWithin xs.toList ys.toList t s := by
  obtain ⟨e, _, hr⟩ := run_compile h.toControl
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact ⟨n, (congrArg (compile p).halt hr.1).trans rfl, (congrArg Cfg.output hl).trans ho,
    ((compile p).length_runHistory_le _ n).trans hn,
    (congrArg History.space hr.2).le.trans hs⟩

end Complexity.TM.Program
