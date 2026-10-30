/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Correctness
public import Complexity.Models.TreeMachine.Deterministic
public import Complexity.Control.Program.WP

/-! # Resource bounds for tree-register programs

History records intermediate register banks, including the temporary pair used by copying.
Specifications use unit time; the machine's size-cost bound follows from `toSizeCost`.
-/

@[expose] public section

namespace Complexity.TreeMachine.Program

open Controller (History)
open Std.WP

variable {k : ℕ} {α : Type}

/-- Record register actions independently of the generated control states. -/
@[simps -fullyApplied eval observe act]
def historySemantics : Program.Semantics (Fin k → Bool) (TreeMachine.Op k) (Op k) Op.Result
    (History (Cfg k Unit) (Action k Unit)) where
  eval := eval
  observe := observe
  act o h := h.snoc (.assign () o)

theorem exec_act_history (o : TreeMachine.Op k)
    (h : History (Cfg k Unit) (Action k Unit)) :
    (act o).Exec historySemantics h 1 () (h.snoc (.assign () o)) :=
  Program.Exec.perform historySemantics (.act o) h

/-- An instruction consumes one unit of time and records its resulting register bank. -/
@[spec]
theorem spec_act (o : TreeMachine.Op k) (s : History (Cfg k Unit) (Action k Unit))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((act o).verify historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = s.snoc (.assign () o) ∧ c = b - 1) x :=
  Program.spec_perform (Op.act o) historySemantics s b hb x

/-- A root test costs one transition and leaves the register bank unchanged. -/
@[spec]
theorem spec_root (i : Fin k) (s : History (Cfg k Unit) (Action k Unit))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((root i).verify historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = (s.last.regs i).root ∧ t = s.snoc (.keep ()) ∧ c = b - 1) x :=
  Program.spec_perform (Op.root i) historySemantics s b hb x

/-- Compilation preserves the endpoint and any peak measurement of register values. -/
theorem run_compile_history {β : Type*} [SemilatticeSup β] (size : (Fin k → Tree) → β)
    {p : TreeMachine.Program k α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg k Unit) (Action k Unit)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result
      historySemantics.observe historySemantics.act q s n a t)
    (u : History (Cfg k (p.State ⊕ p.Exit)) (Action k (p.State ⊕ p.Exit)))
    (hc : u.last = ⟨q, s.last.regs⟩)
    (hs : u.configSup (size ∘ Cfg.regs) = s.configSup (size ∘ Cfg.regs)) :
    ∃ e, p.result e = a ∧ (p.compile.runFrom u n).last = ⟨.inr e, t.last.regs⟩ ∧
      (p.compile.runFrom u n).configSup (size ∘ Cfg.regs) =
        t.configSup (size ∘ Cfg.regs) := by
  induction h generalizing u with
  | done e s => exact ⟨e, rfl, hc, hs⟩
  | step q s h ih =>
    have hstep : p.compile.step u =
        let next := (p.toControl eval).next q (observe s)
        u.snoc (.assign next.2 next.1) := by
      have ho : (observe u : Fin k → Bool) = observe s := by
        funext i
        simp [History.observe_def, Cfg.observe_def, hc]
      rw [Controller.step_eq, History.state_def, Cfg.state_def, hc, ho]
      rfl
    apply ih (p.compile.step u) <;>
      simp [hstep, hc, hs]

/-- A history specification gives actual unit time and peak space for the compiled machine. -/
theorem computesInUnitTimeAndSpace_of_exec [NeZero k] {p : TreeMachine.Program k α}
    {x y : Tree} {n t s : ℕ} {a : α} {v : History (Cfg k Unit) (Action k Unit)}
    (h : p.Exec historySemantics (History.nil ⟨(), input 0 x⟩) n a v)
    (hn : n ≤ t) (ho : v.last.regs 0 = y) (hs : v.configSup Cfg.mass ≤ s) :
    p.compile.ComputesInUnitTimeAndSpace x y t s := by
  obtain ⟨e, _, hc, hv⟩ := run_compile_history (fun ρ ↦ ∑ i, (ρ i).size) h.toControl
    (History.nil (p.compile.initInput (Config := Cfg k _) x)) rfl (by simp)
  simp only [Controller.runFrom_nil, Controller.last_runHistoryFrom] at hc hv
  exact ⟨n, (congrArg (p.compile.halt ∘ Cfg.state) hc).trans rfl,
    (congrArg (fun c ↦ c.regs 0) hc).trans ho,
    (p.compile.length_runHistory_le _ _ n).trans hn, hv.le.trans hs⟩

/-- A program contract yields the machine bound without inspecting compiled control states. -/
theorem computesInUnitTimeAndSpace [NeZero k] {p : TreeMachine.Program k α}
    {x y : Tree} {t s : ℕ} {P : History (Cfg k Unit) (Action k Unit) → ℕ → Prop}
    (h : Triple (p.verify historySemantics) P
      (fun _ v _ ↦ v.last.regs 0 = y ∧ v.configSup Cfg.mass ≤ s) ())
    (hp : P (History.nil ⟨(), input 0 x⟩) t) :
    p.compile.ComputesInUnitTimeAndSpace x y t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Program.exec_of_spec h hp
  exact computesInUnitTimeAndSpace_of_exec he hn ho hs

end Complexity.TreeMachine.Program
