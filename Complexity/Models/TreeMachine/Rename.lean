/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Cost
public import Complexity.Control.Controller.Simulation

/-!
# Running a tree machine on some registers of a larger bank

`M.rename e` runs `M` on the registers `e i` of a bank of `r` registers: it observes and writes
only those, and the other registers keep their trees. For an injective `e`, its runs are those of
`M` on the registers `e i` (`runFrom_rename`), with the same size charges (`actionSum_rename`), so
the other registers can hold a frame while `M` runs. The configurations are written with
`Cfg.extend`, which places a bank of `M` on the registers `e i` and takes the others from a given
bank.
-/

@[expose] public section

namespace Complexity.TreeMachine

universe u

variable {F : Type u → Type*} {k r : ℕ} {Q : Type u}

/-- Run `M` on the registers `e i` of a bank of `r` registers: it observes and writes only those
registers, and the others keep their trees. -/
def rename [Functor F] (M : TreeMachine F k Q) (e : Fin k → Fin r) : TreeMachine F r Q where
  q₀ := M.q₀
  halt := M.halt
  transition q v := Prod.map id (Action.rename e) <$> M.transition q (v ∘ e)

/-- The bank holding `c` in the registers `e i` and the trees of `σ` in the other registers. -/
noncomputable def Cfg.extend (e : Fin k → Fin r) (c : Cfg k) (σ : Fin r → Tree) : Cfg r :=
  ⟨Function.extend e c.regs σ⟩

variable {e : Fin k → Fin r}

/-- The register `e i` of `c.extend e σ` holds the register `i` of `c`. -/
theorem Cfg.extend_regs_apply (he : e.Injective) (c : Cfg k) (σ : Fin r → Tree) (i : Fin k) :
    (c.extend e σ).regs (e i) = c.regs i :=
  he.extend_apply c.regs σ i

/-- The registers outside the image of `e` hold the trees of `σ`. -/
theorem Cfg.extend_regs_of_notMem_range (c : Cfg k) (σ : Fin r → Tree) {j : Fin r}
    (hj : j ∉ Set.range e) : (c.extend e σ).regs j = σ j :=
  Function.extend_apply' c.regs σ j hj

/-- The registers `e i` of `c.extend e σ` hold `c`. -/
theorem Cfg.extend_regs_comp (he : e.Injective) (c : Cfg k) (σ : Fin r → Tree) :
    (c.extend e σ).regs ∘ e = c.regs :=
  Function.extend_comp he c.regs σ

/-- A bank whose registers `e i` already hold `c` is `c` placed in it. -/
theorem Cfg.extend_eq (he : e.Injective) {c : Cfg k} {σ : Fin r → Tree} (h : σ ∘ e = c.regs) :
    c.extend e σ = ⟨σ⟩ := by
  ext j : 2
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [Cfg.extend_regs_apply he, ← h]
    rfl
  · exact Cfg.extend_regs_of_notMem_range c σ hj

/-- An instruction renamed along `e` acts on the registers `e i` as the instruction acts on `c`,
and keeps the other registers. -/
theorem Cfg.apply_rename_extend (he : e.Injective) (o : Action k) (c : Cfg k)
    (σ : Fin r → Tree) : apply (o.rename e) (c.extend e σ) = (apply o c).extend e σ := by
  ext j : 2
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    have h := congrFun (o.eval_rename e he (c.extend e σ).regs) i
    rw [Cfg.extend_regs_comp he] at h
    rw [Cfg.apply_regs, Cfg.extend_regs_apply he, Cfg.apply_regs]
    exact h
  · have hd : (o.rename e).dst ≠ some j := by
      rw [Action.dst_rename]
      rintro h
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact hj ⟨i, rfl⟩
    rw [Action.regs_apply_of_ne _ _ hd, Cfg.extend_regs_of_notMem_range _ σ hj,
      Cfg.extend_regs_of_notMem_range _ σ hj]

/-- The registers `e i` of `c.extend e σ` show the roots of `c`. -/
theorem Cfg.observe_extend_comp (he : e.Injective) (c : Cfg k) (σ : Fin r → Tree) :
    (observe (c.extend e σ) : Fin r → Bool) ∘ e = observe c := by
  funext i
  rw [Function.comp_apply, Cfg.observe_def, Cfg.observe_def, Cfg.extend_regs_apply he]

variable (M : TreeMachine Id k Q) (σ : Fin r → Tree)

/-- A step of `M.rename e` is a step of `M` on the registers `e i`. -/
theorem step_rename (he : e.Injective) (c : Q × Cfg k) :
    (M.rename e).step (c.1, c.2.extend e σ) = ((M.step c).1, (M.step c).2.extend e σ) := by
  by_cases hc : M.halt c.1 = true
  · simp [step_eq, rename, hc]
  · have h' : M.halt c.1 = false := Bool.eq_false_iff.mpr hc
    simp [step_eq, rename, h', Cfg.observe_extend_comp he, Cfg.apply_rename_extend he,
      Controller.apply_prod]

/-- The frame: `M.rename e` runs as `M` on the registers `e i` and keeps the other registers. -/
theorem runFrom_rename (he : e.Injective) (c : Q × Cfg k) (n : ℕ) :
    (M.rename e).runFrom (c.1, c.2.extend e σ) n =
      ((M.runFrom c n).1, (M.runFrom c n).2.extend e σ) :=
  Controller.rel_runFrom M (M.rename e)
    (R := fun (c : Q × Cfg k) (d : Q × Cfg r) ↦ d = (c.1, c.2.extend e σ))
    (by rintro c _ rfl; exact step_rename M σ he c) rfl n

/-- `M.rename e` is charged as `M`. -/
theorem actionSum_rename (he : e.Injective) (c : Q × Cfg k) (n : ℕ) :
    ((M.rename e).runHistoryFrom (c.1, c.2.extend e σ) n).snd.actionSum Action.sizeCost =
      (M.runHistoryFrom c n).snd.actionSum Action.sizeCost := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Controller.actionSum_runHistoryFrom_add, Controller.actionSum_runHistoryFrom_add, ih,
      runFrom_rename M σ he]
    simp [Controller.actionSum_runHistoryFrom_one, rename, Cfg.observe_extend_comp he,
      Action.sizeCost_rename, Cfg.extend_regs_comp he]

end Complexity.TreeMachine
