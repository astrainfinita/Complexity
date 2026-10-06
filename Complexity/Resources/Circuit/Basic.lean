/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Composition
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Circuit depth

Inputs have depth zero. Each operation gate, including a constant, adds one to the maximum depth
of its arguments. Circuit depth is the maximum depth of its designated outputs, so a circuit
with no outputs has depth zero and unused gates need not contribute to depth.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

variable {L : Language} {n m k : ℕ}

/-- Propagate an arbitrary input-depth assignment through a circuit. -/
def evalDepth (c : Circuit L n m) (x : Fin n → ℕ) : Fin m → ℕ :=
  c.evalWith (fun _ args => Finset.univ.sup args + 1) x

/-- The depth of each designated output, with inputs at depth zero. -/
def outputDepths (c : Circuit L n m) : Fin m → ℕ := c.evalDepth fun _ => 0

/-- The maximum depth of the designated outputs. -/
def depth (c : Circuit L n m) : ℕ := Finset.univ.sup c.outputDepths

@[simp] theorem depth_le_iff (c : Circuit L n m) (b : ℕ) :
    c.depth ≤ b ↔ ∀ i, c.outputDepths i ≤ b := by simp [depth, Finset.sup_le_iff]

theorem outputDepths_le_depth (c : Circuit L n m) (i : Fin m) :
    c.outputDepths i ≤ c.depth := Finset.le_sup (Finset.mem_univ i)

@[simp] theorem depth_outputs (select : Fin m → Fin n) :
    (outputs select : Circuit L n m).depth = 0 := by
  simp [depth, outputDepths, evalDepth, Function.comp_def]

@[simp] theorem depth_zero_outputs (c : Circuit L n 0) : c.depth = 0 := by
  simp [depth]

/-- Each stored gate increases an upper bound on all available depths by at most one. -/
theorem evalDepth_le_size_add (c : Circuit L n m) (x : Fin n → ℕ) (b : ℕ)
    (hx : ∀ i, x i ≤ b) (j : Fin m) : c.evalDepth x j ≤ c.size + b := by
  induction c generalizing b with
  | outputs select => simpa [evalDepth, Function.comp_def] using hx (select j)
  | @gate n m k op args next ih =>
      have hg : Finset.univ.sup (x ∘ args) + 1 ≤ b + 1 :=
        Nat.add_le_add_right (Finset.sup_le fun i _ => hx (args i)) 1
      have he : ∀ i : Fin (n + 1),
          Fin.snoc (α := fun _ => ℕ) x (Finset.univ.sup (x ∘ args) + 1) i ≤ b + 1 := by
        intro i
        refine Fin.lastCases ?_ (fun t => ?_) i
        · simpa using hg
        · simpa using (hx t).trans (Nat.le_succ b)
      have h := ih (Fin.snoc x (Finset.univ.sup (x ∘ args) + 1)) (b + 1) he j
      simpa [evalDepth, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Circuit depth is bounded by the number of stored gates, for arbitrary finite arities. -/
theorem depth_le_size (c : Circuit L n m) : c.depth ≤ c.size := by
  apply (depth_le_iff _ _).mpr
  intro j
  simpa [outputDepths] using c.evalDepth_le_size_add (fun _ => 0) 0 (fun _ => le_rfl) j

/-- A bound on the depths of selected outputs is enough; dead gates are irrelevant. -/
theorem depth_mapOutputs_le (c : Circuit L n m) (f : Fin k → Fin m) :
    (c.mapOutputs f).depth ≤ c.depth := by
  apply (depth_le_iff _ _).mpr
  intro i
  simpa [outputDepths, evalDepth] using c.outputDepths_le_depth (f i)

/-- Relabeling input wires preserves output depths. -/
@[simp] theorem depth_relabel (c : Circuit L n m) (f : Fin n → Fin k) :
    (c.relabel f).depth = c.depth := by simp [depth, outputDepths, evalDepth, Function.comp_def]

/-- Increasing every input depth by at most `b` increases each output depth by at most `b`.
This inequality also covers constants, whose depths do not depend on the inputs. -/
theorem evalDepth_le_evalDepth_add (c : Circuit L n m) (x y : Fin n → ℕ) (b : ℕ)
    (h : ∀ i, x i ≤ y i + b) (j : Fin m) : c.evalDepth x j ≤ c.evalDepth y j + b := by
  induction c with
  | outputs select => exact h (select j)
  | @gate n m k op args next ih =>
      have hg : Finset.univ.sup (x ∘ args) ≤ Finset.univ.sup (y ∘ args) + b := by
        apply Finset.sup_le
        intro i _
        exact (h (args i)).trans
          (Nat.add_le_add_right (Finset.le_sup (f := y ∘ args) (Finset.mem_univ i)) b)
      apply ih
      intro i
      refine Fin.lastCases ?_ (fun t => ?_) i
      · simpa only [Fin.snoc_last] using Nat.add_le_add_right hg 1 |>.trans_eq
          (by omega)
      · simpa only [Fin.snoc_castSucc] using h t

/-- Sequential composition has depth at most the sum of the two depths. -/
theorem depth_comp_le (c : Circuit L n m) (d : Circuit L m k) :
    (c.comp d).depth ≤ c.depth + d.depth := by
  apply (depth_le_iff _ _).mpr
  intro j
  have h := d.evalDepth_le_evalDepth_add c.outputDepths (fun _ => 0) c.depth
    (fun i => by simpa using c.outputDepths_le_depth i) j
  have hj := d.outputDepths_le_depth j
  simp only [outputDepths, evalDepth, evalWith_comp] at h hj ⊢
  omega

end Complexity.Circuit
