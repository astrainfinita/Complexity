/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Basic
public import Complexity.Models.TreeMachine.Deterministic
public import Complexity.Control.Program.Correctness
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

variable {F : Type → Type} {k : ℕ} {α : Type}

/-- Record register actions independently of the generated control states. -/
@[simps -fullyApplied eval observe act]
def historySemantics : Program.Semantics (Fin k → Bool) (TreeMachine.Action k) (Op k) Op.Result
    (History (Cfg k) (TreeMachine.Action k)) where
  eval := eval
  observe := observe
  act o h := h.snoc o

section Verify

variable {m : Type → Type} [Monad m] {Q : MonadQuant m} [MonadLiftT F m]

/-- An instruction consumes one unit of time and records its resulting register bank. -/
@[spec]
theorem spec_act (o : TreeMachine.Action k) (s : History (Cfg k) (TreeMachine.Action k))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((act (F := F) o).verifyWith m Q historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = s.snoc o ∧ c = b - 1) x :=
  Program.spec_perform (Op.act o) historySemantics s b hb x

/-- A root test costs one transition and leaves the register bank unchanged. -/
@[spec]
theorem spec_root (i : Fin k) (s : History (Cfg k) (TreeMachine.Action k))
    (b : ℕ) (hb : 0 < b) (x : Unit) :
    Triple ((root (F := F) i).verifyWith m Q historySemantics) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = (s.last.regs i).root ∧ t = s.snoc TreeMachine.Action.nop ∧ c = b - 1) x :=
  Program.spec_perform (Op.root i) historySemantics s b hb x

variable {s : History (Cfg k) (TreeMachine.Action k)}

/-- An instruction takes one step and records its resulting register bank. -/
theorem execWithinWith_act {o : TreeMachine.Action k}
    {P : Unit → History (Cfg k) (TreeMachine.Action k) → Prop} (h : P () (s.snoc o)) :
    (act (F := F) o).ExecWithinWith m Q historySemantics s 1 fun r t _ ↦ P r t :=
  .step _ _ _ 0 (.ret _ _ _ h)

/-- An instruction followed by a continuation takes one step more than the continuation run on
the resulting register bank. -/
theorem execWithinWith_act_bind {o : TreeMachine.Action k}
    {f : Unit → TreeMachine.Program F k α} {b : ℕ}
    {R : α → History (Cfg k) (TreeMachine.Action k) → ℕ → Prop}
    (h : (f ()).ExecWithinWith m Q historySemantics (s.snoc o) b R) :
    (act o >>= f).ExecWithinWith m Q historySemantics s (b + 1) R :=
  .step _ _ _ _ h

/-- A root test takes one no-op step and returns the root of the register. -/
theorem execWithinWith_root {i : Fin k}
    {P : Bool → History (Cfg k) (TreeMachine.Action k) → Prop}
    (h : P (s.last.regs i).root (s.snoc .nop)) :
    (root (F := F) i).ExecWithinWith m Q historySemantics s 1 fun r t _ ↦ P r t :=
  .step _ _ _ 0 (.ret _ _ _ h)

end Verify

/-- A history execution within the time budget gives actual unit time and peak space for the
compiled machine. -/
theorem computesWithinUnitTime_of_execWithin [NeZero k] {p : TreeMachine.Program Id k α}
    {x y : Tree} {t s : ℕ}
    (h : p.ExecWithin historySemantics (History.nil (Cfg.init k x)) t
      (fun _ v _ ↦ v.last.regs 0 = y ∧ v.configSup Cfg.mass ≤ s)) :
    p.compile.ComputesWithinUnitTime x y t s := by
  obtain ⟨e, v, hr, -, -, ho, hs⟩ := Program.Syntax.ExecWithin.runFrom_compile .nop h
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact .of_halted t ((congrArg p.compile.halt hr.1).trans rfl)
    ((congrArg (fun c ↦ c.regs 0) hl).trans ho)
    ((History.length_snd _).trans_le (p.compile.length_runHistory_le x t))
    ((congrArg (·.configSup Cfg.mass) hr.2).le.trans hs)

/-- A program contract yields the machine bound without inspecting compiled control states. -/
theorem computesWithinUnitTime [NeZero k] {p : TreeMachine.Program Id k α}
    {x y : Tree} {t s : ℕ} {P : History (Cfg k) (TreeMachine.Action k) → ℕ → Prop}
    (h : Triple (p.verify historySemantics) P
      (fun _ v _ ↦ v.last.regs 0 = y ∧ v.configSup Cfg.mass ≤ s) ())
    (hp : P (History.nil (Cfg.init k x)) t) :
    p.compile.ComputesWithinUnitTime x y t s :=
  computesWithinUnitTime_of_execWithin (Program.execWithinWith_of_spec h hp)

end Complexity.TreeMachine.Program
