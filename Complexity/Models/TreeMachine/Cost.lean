/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Complexity.Control.Controller.History.Cost
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size costs for tree registers

Projections cost the expanded source size; pairing costs the expanded result size.
A `nop` costs one. The generic controller cost API excludes halting padding.
Space counts all register trees, including one node for each empty leaf.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {k : ℕ}

/-- Total expanded tree size in the register bank, including one node for each `nil`. -/
def Cfg.mass (c : Cfg k) : ℕ := ∑ i, Tree.size (c.regs i)

/-- The other registers each contribute one empty leaf to the initial mass. -/
theorem sum_size_input (i : Fin k) (a : Tree) :
    (∑ j, (input i a j).size) = a.size + (k - 1) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h : ∀ j ∈ Finset.univ.erase i, (input i a j).size = 1 := by
    intro j hj
    simp [input_get_of_ne a (Finset.mem_erase.mp hj).1]
  rw [Finset.sum_congr rfl h]
  simp [Nat.add_comm]

/-- Each register contributes at most the total expanded size. -/
theorem Cfg.reg_size_le_mass (c : Cfg k) (i : Fin k) : (c.regs i).size ≤ c.mass :=
  Finset.single_le_sum (f := fun j ↦ (c.regs j).size)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- The peak total size is bounded by the sum of the individual register peaks. -/
theorem configSup_mass_le_sum (h : Controller.History (Cfg k) (Action k)) :
    h.configSup Cfg.mass ≤ ∑ i, h.configSup (fun c ↦ (c.regs i).size) :=
  (h.configSup_le_iff Cfg.mass _).2 fun _ hc ↦
    Finset.sum_le_sum fun i _ ↦ h.config_le_configSup (fun c ↦ (c.regs i).size) hc

/-- Projections pay for reading their source; pairing pays for constructing its result. -/
def Action.sizeCost (o : Action k) (c : Cfg k) : ℕ :=
  match o with
  | .nop => 1
  | .left _ j | .right _ j => (c.regs j).size
  | .pair _ j l => (Tree.pair (c.regs j) (c.regs l)).size

/-- Every active instruction incurs a positive charge. -/
theorem Action.sizeCost_pos (o : Action k) (c : Cfg k) : 0 < o.sizeCost c := by
  cases o <;> simp only [sizeCost] <;> first | exact Nat.zero_lt_one | exact Tree.size_pos _

/-- A write's charge covers the size of the value produced. -/
theorem Action.written_size_le {o : Action k} {c : Cfg k} {i : Fin k}
    (h : o.dst = some i) : (o.eval c.regs i).size ≤ o.sizeCost c := by
  cases o <;> simp_all only [dst, Option.some.injEq, reduceCtorEq, eval,
    Function.update_self, sizeCost]
  all_goals first | exact Tree.size_left_le _ | exact Tree.size_right_le _ | exact le_rfl

/-- An update exchanges exactly the old and new destination sizes. -/
theorem Action.sum_size_eval_add (o : Action k) (ρ : Fin k → Tree) {i : Fin k}
    (h : o.dst = some i) :
    (∑ j, (o.eval ρ j).size) + (ρ i).size =
      (∑ j, (ρ j).size) + (o.eval ρ i).size := by
  have he : ∑ j ∈ Finset.univ.erase i, (o.eval ρ j).size =
      ∑ j ∈ Finset.univ.erase i, (ρ j).size := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [o.eval_of_dst_ne ρ j (by simp [h, Ne.symm (Finset.mem_erase.mp hj).1])]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), he,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  omega

/-- Instruction costs depend only on the trees in the renamed registers. -/
theorem Action.sizeCost_rename {l : ℕ} (f : Fin k → Fin l) (c : Cfg l) (o : Action k) :
    (o.rename f).sizeCost c = o.sizeCost ⟨c.regs ∘ f⟩ := by
  cases o <;> simp [sizeCost, rename]

/-- A register's new peak is bounded by its previous peak and the instruction's charge. -/
theorem configSup_reg_size_snoc_le (h : Controller.History (Cfg k) (Action k)) (o : Action k)
    (i : Fin k) :
    (h.snoc o).configSup (fun c ↦ (c.regs i).size) ≤
      h.configSup (fun c ↦ (c.regs i).size) ⊔ o.sizeCost h.last := by
  rw [Controller.History.configSup_snoc]
  apply sup_le le_sup_left
  by_cases hd : o.dst = some i
  · exact (o.written_size_le hd).trans le_sup_right
  · rw [Cfg.apply_regs, o.eval_of_dst_ne _ _ hd]
    exact (h.config_le_configSup (fun c ↦ (c.regs i).size) h.last_mem_configs).trans le_sup_left

/-- Each instruction's charge pays for the possible increase in total register size. -/
theorem Cfg.mass_apply_le (c : Cfg k) (o : Action k) :
    (apply o c).mass ≤ c.mass + o.sizeCost c := by
  cases hd : o.dst with
  | none =>
    have ho : o = .nop := by cases o <;> simp_all
    simp [mass, Action.sizeCost, ho]
  | some i =>
    have he := o.sum_size_eval_add c.regs hd
    have hb := o.written_size_le (c := c) hd
    rw [mass, mass, Cfg.apply_regs]
    omega

/-- A `nop` does not change any peak measurement of the register bank. -/
@[simp↓] theorem configSup_snoc_nop {β : Type*} [SemilatticeSup β]
    (h : Controller.History (Cfg k) (Action k)) (f : Cfg k → β) :
    (h.snoc .nop).configSup f = h.configSup f := by
  simpa only [Controller.History.configSup_snoc, Action.apply_nop]
    using sup_eq_left.mpr (h.config_le_configSup f h.last_mem_configs)

/-- Each charge is bounded by the larger of the adjacent register masses. -/
theorem Action.sizeCost_le_mass [NeZero k] (o : Action k) (c : Cfg k) :
    o.sizeCost c ≤ c.mass ⊔ (apply o c).mass := by
  cases o with
  | nop => exact (Tree.size_pos (c.regs 0)).trans_le ((c.reg_size_le_mass 0).trans le_sup_left)
  | left i j | right i j => exact (c.reg_size_le_mass j).trans le_sup_left
  | pair i j l =>
    have h := (apply (Action.pair i j l) c).reg_size_le_mass i
    rw [Cfg.apply_regs, Action.eval_pair, Function.update_self] at h
    exact h.trans le_sup_right

theorem length_le_actionSum (h : Controller.History (Cfg k) (Action k)) :
    h.length ≤ h.actionSum Action.sizeCost := by
  rw [← h.actionSum_unit]
  exact h.actionSum_mono fun o c _ ↦ Nat.succ_le_of_lt (o.sizeCost_pos c)

/-- Size-charged time is bounded by unit time times peak expanded-tree space. -/
theorem actionSum_le_length_mul_mass [NeZero k] (h : Controller.History (Cfg k) (Action k)) :
    h.actionSum Action.sizeCost ≤ h.length * h.configSup Cfg.mass :=
  h.actionSum_le_length_mul_configSup _ _ fun o c _ ↦ o.sizeCost_le_mass c

end Complexity.TreeMachine
