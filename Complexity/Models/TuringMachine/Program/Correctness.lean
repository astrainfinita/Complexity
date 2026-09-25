/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Basic
public import Complexity.Control.Program.Correctness
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

variable {κ : Type} {Γ α : Type} [Inhabited Γ] {xs : Array Γ}

/-- A compiled step preserves the complete tracked state and updates its control label. -/
@[simp]
theorem step_compile (p : Program κ Γ α) (q : p.State)
    (s : TrackedCfg κ Γ Unit xs) :
    (compile p).step (s.mapState (fun _ ↦ Sum.inl q)) =
      let next := (Complexity.Program.compile eval p).next q (Controller.observe s)
      (apply next.1 s).mapState (fun _ ↦ next.2) := rfl

/-- Compilation preserves the complete configuration, including any earlier visit history. -/
theorem run_compile {p : Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : TrackedCfg κ Γ Unit xs} {n : ℕ} {a : α}
    (h : Complexity.Program.Control.Run (Complexity.Program.compile eval p) p.result
      Controller.observe (apply) q s n a t) :
    ∃ e : p.Exit, p.result e = a ∧
      (compile p).runFrom (s.mapState (fun _ ↦ q)) n = t.mapState (fun _ ↦ Sum.inr e) := by
  induction h with
  | done e s => exact ⟨e, rfl, rfl⟩
  | step q s h ih =>
    obtain ⟨e, he, hr⟩ := ih
    refine ⟨e, he, ?_⟩
    rw [Controller.runFrom_succ, step_compile]
    exact hr

/-- The compiled run's peak space is the final recorded space, including earlier history. -/
theorem runConfigMaxFrom_compile [Fintype κ] {p : Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : TrackedCfg κ Γ Unit xs} {n : ℕ} {a : α}
    (h : Complexity.Program.Control.Run (Complexity.Program.compile eval p) p.result
      Controller.observe (apply) q s n a t) :
    (compile p).runConfigMaxFrom visitedCosts.space (s.mapState (fun _ ↦ q)) n =
      t.space := by
  obtain ⟨_, _, hr⟩ := run_compile h
  rw [runConfigMaxFrom_tracked, hr, TrackedCfg.space_mapState]

/-- A source execution gives a machine computation with the same time and bounded space. -/
theorem computesInTimeAndSpace_of_exec [Fintype κ] (p : Program κ Γ α) {ys : Array Γ}
    {n t s : ℕ} {a : α} {v : TrackedCfg κ Γ Unit xs}
    (h : Complexity.Program.Syntax.Exec
      (⟨eval, Controller.observe, apply⟩ :
        Complexity.Program.Semantics _ _ _ _ _)
      p ((rawExecution xs.toList).init ()).track n a v)
    (hn : n ≤ t) (ho : v.cfg.output = ys) (hs : v.space ≤ s) :
    (compile p).ComputesInTimeAndSpace xs.toList ys.toList t s := by
  obtain ⟨e, _, hr⟩ := run_compile (h.compile _)
  apply TM.ReachesInTimeAndSpace.computesInTimeAndSpace
    (M := compile p) (d := v.cfg.mapState (fun _ ↦ Sum.inr e)) ?_ (by rfl) ho
  refine ⟨n, hn, ?_, ?_⟩
  · exact ((compile p).tracked_runFrom_cfg _ n).symm.trans (congrArg TrackedCfg.cfg hr)
  · exact (runConfigMaxFrom_compile (h.compile _)).le.trans hs

end Complexity.TM.Program
