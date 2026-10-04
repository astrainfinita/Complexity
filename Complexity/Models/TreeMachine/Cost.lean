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

An instruction costs the expanded size of the tree written to its destination.
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

/-- The size written to the destination, or one for a control-only instruction. -/
def Op.sizeCost (o : Op k) (ρ : Fin k → Tree) : ℕ :=
  match o.dst with
  | none => 1
  | some i => (o.eval ρ i).size

/-- Every active instruction incurs a positive charge, including writes of `nil`. -/
theorem Op.sizeCost_pos (o : Op k) (ρ : Fin k → Tree) : 0 < o.sizeCost ρ := by
  unfold sizeCost
  split
  · decide
  · exact Tree.size_pos _

/-- Instruction costs depend only on the trees in the renamed registers. -/
theorem Op.sizeCost_rename {l : ℕ} (f : Fin k → Fin l) (ρ : Fin l → Tree) (o : Op k) :
    (o.rename f).sizeCost ρ = o.sizeCost (ρ ∘ f) := by
  cases o <;> simp [sizeCost, rename, eval, Function.comp_def]

/-- The charge for the instruction selected at this configuration. -/
def Action.sizeCost (a : Action k Q) (c : Cfg k Q) : ℕ := a.op.sizeCost c.regs

/-- The destination is part of the next register bank; `nop` costs one leaf. -/
theorem Action.sizeCost_le_mass_apply [NeZero k] (a : Action k Q) (c : Cfg k Q) :
    a.sizeCost c ≤ (apply a c).mass := by
  unfold sizeCost Op.sizeCost
  cases hd : a.op.dst with
  | none =>
    exact (Tree.size_pos ((apply a c).regs 0)).trans_le ((apply a c).reg_size_le_mass 0)
  | some i => exact (apply a c).reg_size_le_mass i

theorem length_le_actionSum (h : Controller.History (Cfg k Q) (Action k Q)) :
    h.length ≤ h.actionSum Action.sizeCost := by
  rw [← h.actionSum_unit]
  exact h.actionSum_mono fun a c _ ↦ Nat.succ_le_of_lt (Op.sizeCost_pos a.op c.regs)

/-- Destination-size time is bounded by unit time times peak expanded-tree space. -/
theorem actionSum_le_length_mul_mass [NeZero k]
    (h : Controller.History (Cfg k Q) (Action k Q)) :
    h.actionSum Action.sizeCost ≤ h.length * h.configSup Cfg.mass :=
  h.actionSum_le_length_mul_configSup _ _ fun a c _ ↦ a.sizeCost_le_mass_apply c

private theorem sum_size_update_le (ρ : Fin k → Tree) (i : Fin k) (a : Tree) :
    (∑ j, (Function.update ρ i a j).size) ≤ (∑ j, (ρ j).size) + a.size := by
  calc
    _ ≤ ∑ j, ((ρ j).size + if j = i then a.size else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i <;> simp [h]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Each instruction's charge pays for the possible increase in total register size. -/
theorem Cfg.mass_apply_le (c : Cfg k Q) (a : Action k Q) :
    (apply a c).mass ≤ c.mass + a.sizeCost c := by
  rcases a with ⟨o, q⟩
  cases o with
  | nop => simp [mass, Action.sizeCost, Op.sizeCost]
  | left i j => simpa [mass, Action.sizeCost, Op.sizeCost] using
      sum_size_update_le c.regs i (c.regs j).left
  | right i j => simpa [mass, Action.sizeCost, Op.sizeCost] using
      sum_size_update_le c.regs i (c.regs j).right
  | pair i j l => simpa [mass, Action.sizeCost, Op.sizeCost] using
      sum_size_update_le c.regs i (.pair (c.regs j) (c.regs l))

end Complexity.TreeMachine
