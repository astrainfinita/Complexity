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
The compiled machine records the same history.
Specifications use unit time; the machine's size-cost bound follows from `toSizeCost`.
-/

@[expose] public section

namespace Complexity.TreeMachine.Program

open Controller (History)
open Std.WP

variable {k : ℕ} {α : Type}

/-- Record register actions independently of the generated control states. -/
@[simps -fullyApplied eval observe act]
def historySemantics : Program.Semantics (Fin k → Bool) (TreeMachine.Action k) (Op k) Op.Result
    (History (Cfg k) (TreeMachine.Action k)) where
  eval := eval
  observe := observe
  act o h := h.snoc o

theorem exec_act_history (o : TreeMachine.Action k)
    (h : History (Cfg k) (TreeMachine.Action k)) :
    (act o).Exec historySemantics h 1 () (h.snoc o) :=
  Program.Exec.perform historySemantics (.act o) h

/-- An instruction consumes one unit of time and records its resulting register bank. -/
@[spec]
theorem spec_act (o : TreeMachine.Action k) (s : History (Cfg k) (TreeMachine.Action k))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((act o).verify historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = s.snoc o ∧ c = b - 1) x :=
  Program.spec_perform (Op.act o) historySemantics s b hb x

/-- A root test costs one transition and leaves the register bank unchanged. -/
@[spec]
theorem spec_root (i : Fin k) (s : History (Cfg k) (TreeMachine.Action k))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((root i).verify historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = (s.last.regs i).root ∧ t = s.snoc TreeMachine.Action.nop ∧ c = b - 1) x :=
  Program.spec_perform (Op.root i) historySemantics s b hb x

/-- Running the compiled machine on a history records the program's history. -/
theorem run_compile_history {p : TreeMachine.Program k α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg k) (TreeMachine.Action k)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result
      historySemantics.observe historySemantics.act q s n a t) :
    ∃ e, p.result e = a ∧ p.compile.runFrom (q, s) n = (.inr e, t) := by
  induction h with
  | done e s => exact ⟨e, rfl, rfl⟩
  | step q s h ih => exact ih

/-- A history specification gives actual unit time and peak space for the compiled machine. -/
theorem computesInUnitTimeAndSpace_of_exec [NeZero k] {p : TreeMachine.Program k α}
    {x y : Tree} {n t s : ℕ} {a : α} {v : History (Cfg k) (TreeMachine.Action k)}
    (h : p.Exec historySemantics (History.nil (Cfg.init k x)) n a v)
    (hn : n ≤ t) (ho : v.last.regs 0 = y) (hs : v.configSup Cfg.mass ≤ s) :
    p.compile.ComputesInUnitTimeAndSpace x y t s := by
  obtain ⟨e, _, hr⟩ := run_compile_history h.toControl
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact ⟨n, (congrArg p.compile.halt hr.1).trans rfl, (congrArg (fun c ↦ c.regs 0) hl).trans ho,
    (p.compile.length_runHistory_le x n).trans hn,
    (congrArg (·.configSup Cfg.mass) hr.2).le.trans hs⟩

/-- A program contract yields the machine bound without inspecting compiled control states. -/
theorem computesInUnitTimeAndSpace [NeZero k] {p : TreeMachine.Program k α}
    {x y : Tree} {t s : ℕ} {P : History (Cfg k) (TreeMachine.Action k) → ℕ → Prop}
    (h : Triple (p.verify historySemantics) P
      (fun _ v _ ↦ v.last.regs 0 = y ∧ v.configSup Cfg.mass ≤ s) ())
    (hp : P (History.nil (Cfg.init k x)) t) :
    p.compile.ComputesInUnitTimeAndSpace x y t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Program.exec_of_spec h hp
  exact computesInUnitTimeAndSpace_of_exec he hn ho hs

end Complexity.TreeMachine.Program
