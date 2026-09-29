/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Basic
public import Complexity.Control.Program.Correctness
public import Complexity.Control.Controller.RunHistory
public import Complexity.Models.TuringMachine.Simulation

/-!
# Resource-preserving compilation of finite programs

One program transition is exactly one transition of its compiled machine. The history
maintained by the program semantics covers the machine's visited work cells, including
the initial positions. Thus a total program execution proves actual machine termination,
output correctness, and bounds in `ComputesInTimeAndSpace`.
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

/-- Erasing control labels identifies the compiled history with the source history.
Earlier labels remain intact; only the final label is the returned exit. -/
theorem run_compile {p : TM.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result
      observe (apply) q s n a t)
    (u : History (Cfg κ Γ (p.State ⊕ p.Exit) xs) (Action κ Γ (p.State ⊕ p.Exit)))
    (hu : u.mapState (fun _ ↦ ()) = s) (hq : u.last.state = q) :
    ∃ e : p.Exit, p.result e = a ∧
      ((compile p).runFrom u n).last.state = .inr e ∧
      ((compile p).runFrom u n).mapState (fun _ ↦ ()) = t := by
  induction h generalizing u with
  | done e s => exact ⟨e, rfl, hq, hu⟩
  | step q s h ih =>
    apply ih ((compile p).step u)
    · rw [step_compile p q u hq, ← History.apply_mapState,
        Action.mapState_mapState, ← hu, History.observe_mapState]
      rfl
    · simp only [step_compile p q u hq, History.apply_last, apply_state,
        Action.mapState_state, ← hu, History.observe_mapState]

/-- Compilation preserves space, including visits recorded before the source execution. -/
theorem history_space_compile [Fintype κ] {p : TM.Program κ Γ α}
    {q : p.State ⊕ p.Exit} {s t : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)}
    {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result observe (apply) q s n a t) :
    ((compile p).runFrom (s.mapState (fun _ ↦ q)) n).space = t.space := by
  obtain ⟨_, _, _, hr⟩ := run_compile h (s.mapState (fun _ ↦ q))
    (by rw [History.mapState_mapState]; exact History.mapState_id s) (by simp)
  simpa only [History.space_mapState] using congrArg History.space hr

/-- A source execution proves output, time, and visited-cell space of the compiled machine. -/
theorem computesInTimeAndSpace_of_exec [Fintype κ] (p : TM.Program κ Γ α) {ys : Array Γ}
    {n t s : ℕ} {a : α} {v : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)}
    (h : Program.Syntax.Exec
      (⟨eval, observe, apply⟩ : Program.Semantics _ _ _ _ _)
      p (History.nil ((rawExecution xs.toList).init ())) n a v)
    (hn : n ≤ t) (ho : v.last.output = ys) (hs : v.space ≤ s) :
    (compile p).ComputesInTimeAndSpace xs.toList ys.toList t s := by
  obtain ⟨e, _, hh, hr⟩ := run_compile h.toControl
    (History.nil ((rawExecution xs.toList).init (compile p).q₀)) rfl rfl
  simp only [Controller.runFrom_nil] at hh hr
  simp only [← hr, History.last_mapState, Cfg.mapState_output, History.space_mapState] at ho hs
  simp only [Controller.last_runHistoryFrom] at hh ho
  exact ⟨n, (congrArg (compile p).halt hh).trans rfl, ho,
    ((compile p).runHistory_spec _ _ n).length_le.trans hn, hs⟩

end Complexity.TM.Program
