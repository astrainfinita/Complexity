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

variable {k : ℕ} {Q : Type*}

/-- Total expanded tree size in the register bank, including one node for each `nil`. -/
def Cfg.mass (c : Cfg k Q) : ℕ := ∑ i, Tree.size (c.regs i)

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
theorem Cfg.reg_size_le_mass (c : Cfg k Q) (i : Fin k) : (c.regs i).size ≤ c.mass :=
  Finset.single_le_sum (f := fun j ↦ (c.regs j).size)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Projections pay for reading their source; pairing pays for constructing its result. -/
def Op.sizeCost (o : Op k) (ρ : Fin k → Tree) : ℕ :=
  match o with
  | .nop => 1
  | .left _ j | .right _ j => (ρ j).size
  | .pair _ j l => (Tree.pair (ρ j) (ρ l)).size

/-- Every active instruction incurs a positive charge. -/
theorem Op.sizeCost_pos (o : Op k) (ρ : Fin k → Tree) : 0 < o.sizeCost ρ := by
  cases o <;> simp only [sizeCost] <;> first | exact Nat.zero_lt_one | exact Tree.size_pos _

/-- A write's charge covers the size of the value produced. -/
theorem Op.written_size_le {o : Op k} {ρ : Fin k → Tree} {i : Fin k}
    (h : o.dst = some i) : (o.eval ρ i).size ≤ o.sizeCost ρ := by
  cases o <;> simp_all only [dst, Option.some.injEq, reduceCtorEq, eval,
    Function.update_self, sizeCost]
  all_goals first | exact Tree.size_left_le _ | exact Tree.size_right_le _ | exact le_rfl

/-- An update exchanges exactly the old and new destination sizes. -/
theorem Op.sum_size_eval_add (o : Op k) (ρ : Fin k → Tree) {i : Fin k}
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
theorem Op.sizeCost_rename {l : ℕ} (f : Fin k → Fin l) (ρ : Fin l → Tree) (o : Op k) :
    (o.rename f).sizeCost ρ = o.sizeCost (ρ ∘ f) := by
  cases o <;> simp [sizeCost, rename]

/-- The charge for the instruction selected at this configuration. -/
def Action.sizeCost (a : Action k Q) (c : Cfg k Q) : ℕ := a.op.sizeCost c.regs

/-- Each charge is bounded by the larger of the adjacent register masses. -/
theorem Action.sizeCost_le_mass [NeZero k] (a : Action k Q) (c : Cfg k Q) :
    a.sizeCost c ≤ c.mass ⊔ (apply a c).mass := by
  rcases a with ⟨o, q⟩
  cases o with
  | nop =>
    exact (Tree.size_pos (c.regs 0)).trans_le
      ((c.reg_size_le_mass 0).trans le_sup_left)
  | left i j | right i j => exact (c.reg_size_le_mass j).trans le_sup_left
  | pair i j l =>
    have h := (apply (⟨.pair i j l, q⟩ : Action k Q) c).reg_size_le_mass i
    rw [Cfg.apply_regs, Op.eval_pair, Function.update_self] at h
    exact h.trans le_sup_right

theorem length_le_actionSum (h : Controller.History (Cfg k Q) (Action k Q)) :
    h.length ≤ h.actionSum Action.sizeCost := by
  rw [← h.actionSum_unit]
  exact h.actionSum_mono fun a c _ ↦ Nat.succ_le_of_lt (Op.sizeCost_pos a.op c.regs)

/-- Size-charged time is bounded by unit time times peak expanded-tree space. -/
theorem actionSum_le_length_mul_mass [NeZero k]
    (h : Controller.History (Cfg k Q) (Action k Q)) :
    h.actionSum Action.sizeCost ≤ h.length * h.configSup Cfg.mass :=
  h.actionSum_le_length_mul_configSup _ _ fun a c _ ↦ a.sizeCost_le_mass c

/-- Each instruction's charge pays for the possible increase in total register size. -/
theorem Cfg.mass_apply_le (c : Cfg k Q) (a : Action k Q) :
    (apply a c).mass ≤ c.mass + a.sizeCost c := by
  cases hd : a.op.dst with
  | none =>
    have ho : a.op = .nop := by cases h : a.op <;> simp_all
    simp [mass, Action.sizeCost, Op.sizeCost, ho]
  | some i =>
    have he := a.op.sum_size_eval_add c.regs hd
    have hb := a.op.written_size_le (ρ := c.regs) hd
    change (∑ j, (a.op.eval c.regs j).size) ≤ (∑ j, (c.regs j).size) + a.op.sizeCost c.regs
    omega

end Complexity.TreeMachine
