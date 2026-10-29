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

/-- A compiled transition records its action and its new control label. -/
theorem step_compile (p : TM.Program κ Γ α) (q : p.State)
    (s : History (Cfg κ Γ (p.State ⊕ p.Exit) xs) (Action κ Γ (p.State ⊕ p.Exit)))
    (hs : s.last.state = .inl q) :
    (compile p).step s =
      let next := (p.toControl eval).next q (observe s)
      apply (next.1.mapState (fun _ ↦ next.2)) s := by
  rw [Controller.step_eq, History.state_def, Cfg.state_def, hs]
  rfl

/-- Compilation preserves the final configuration and visited intervals. -/
theorem run_compile {p : TM.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result observe apply q s n a t)
    (u : History (Cfg κ Γ (p.State ⊕ p.Exit) xs) (Action κ Γ (p.State ⊕ p.Exit)))
    (hc : u.last = s.last.mapState (fun _ ↦ q)) (hv : u.visited = s.visited) :
    ∃ e : p.Exit, p.result e = a ∧
      ((compile p).runFrom u n).last = t.last.mapState (fun _ ↦ Sum.inr e) ∧
      ((compile p).runFrom u n).visited = t.visited := by
  induction h generalizing u with
  | done e s => exact ⟨e, rfl, hc, hv⟩
  | step q s h ih =>
    have hq : u.last.state = .inl q := by simp [hc]
    apply ih ((compile p).step u) <;>
      simp [step_compile p q u hq, hc, hv, History.observe_def, Cfg.observe_def]
    rfl

/-- A source execution proves output, time, and visited-cell space of the compiled machine. -/
theorem computesWithin_of_exec [Fintype κ] (p : TM.Program κ Γ α) {ys : Array Γ}
    {n t s : ℕ} {a : α} {v : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)}
    (h : Program.Syntax.Exec
      (⟨eval, observe, apply⟩ : Program.Semantics _ _ _ _ _)
      p (History.nil ((rawExecution xs.toList).init ())) n a v)
    (hn : n ≤ t) (ho : v.last.output = ys) (hs : v.space ≤ s) :
    (compile p).ComputesWithin xs.toList ys.toList t s := by
  obtain ⟨e, _, hc, hv⟩ := run_compile h.toControl
    (History.nil ((rawExecution xs.toList).init (compile p).q₀)) rfl (by simp)
  simp only [Controller.runFrom_nil, Controller.last_runHistoryFrom] at hc hv
  exact ⟨n, (congrArg ((compile p).halt ∘ Cfg.state) hc).trans rfl,
    (congrArg Cfg.output hc).trans ho, ((compile p).runHistory_spec _ _ n).length_le.trans hn,
    (History.space_le_of_visited_le _ _ hv.le).trans hs⟩

end Complexity.TM.Program
