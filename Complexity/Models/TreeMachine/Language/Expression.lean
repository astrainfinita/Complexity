/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Models.TreeMachine.Program.Basic

/-! # Compiling tree expressions with reusable temporary registers -/

@[expose] public section

namespace Complexity.TreeProgram.Expr

variable {ν : Type} {k : ℕ}

/-- The number of temporary registers needed to evaluate an expression. -/
def slots : Expr ν → ℕ
  | .nil | .var _ => 1
  | .left e | .right e => e.slots
  | .pair a b => max a.slots (b.slots + 1)

theorem slots_pos (e : Expr ν) : 0 < e.slots := by
  induction e <;> simp_all [slots]

/-- Evaluate into register `b`, reusing the following registers for subexpressions.
The source layout and the permanently empty register precede these temporaries. -/
def compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program k Unit :=
  let d : Fin k := ⟨b, by have := e.slots_pos; omega⟩
  match e with
  | .nil => TreeMachine.Program.act (.left d z)
  | .var x => TreeMachine.Program.copy z d (v x)
  | .left e => do
      e.compile v z b hb
      TreeMachine.Program.act (.left d d)
  | .right e => do
      e.compile v z b hb
      TreeMachine.Program.act (.right d d)
  | .pair a c => do
      a.compile v z b (by simp only [slots] at hb; omega)
      c.compile v z (b + 1) (by simp only [slots] at hb; omega)
      TreeMachine.Program.act (.pair d d ⟨b + 1, by
        have := c.slots_pos
        simp only [slots] at hb
        omega⟩)

private theorem update_below (ρ : Fin k → Tree) (d i : Fin k) (x : Tree)
    (hi : i.val < d.val) : Function.update ρ d x i = ρ i := by
  have h : i ≠ d := by intro h; subst i; omega
  simp [h]

/-- Compilation computes the source expression and preserves all earlier registers. -/
theorem exec_compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ n σ, (e.compile v z b hb).Exec TreeMachine.Program.semantics ρ n () σ ∧
      σ ⟨b, by have := e.slots_pos; omega⟩ = e.eval (ρ ∘ v) ∧
      ∀ i : Fin k, i.val < b → σ i = ρ i := by
  induction e generalizing b ρ with
  | nil =>
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨1, (TreeMachine.Op.left d z).eval ρ,
        TreeMachine.Program.exec_act _ _, ?_, ?_⟩
      · simp [d, hz]
      · intro i hi
        exact update_below ρ d i _ hi
  | var x =>
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨2, Function.update ρ d (ρ (v x)),
        TreeMachine.Program.exec_copy _ _ _ _, ?_, ?_⟩
      · simp [d]
      · intro i hi
        exact update_below ρ d i _ hi
  | left e ih =>
      obtain ⟨n, σ, hrun, hval, hframe⟩ := ih b hb hv hzv ρ hz
      let d : Fin k := ⟨b, by have := e.slots_pos; change b + e.slots ≤ k at hb; omega⟩
      refine ⟨n + 1, (TreeMachine.Op.left d d).eval σ,
        hrun.bind (TreeMachine.Program.exec_act _ _), ?_, ?_⟩
      · simpa [d] using congrArg BinaryTree.left hval
      · intro i hi
        exact (update_below σ d i _ hi).trans (hframe i hi)
  | right e ih =>
      obtain ⟨n, σ, hrun, hval, hframe⟩ := ih b hb hv hzv ρ hz
      let d : Fin k := ⟨b, by have := e.slots_pos; change b + e.slots ≤ k at hb; omega⟩
      refine ⟨n + 1, (TreeMachine.Op.right d d).eval σ,
        hrun.bind (TreeMachine.Program.exec_act _ _), ?_, ?_⟩
      · simpa [d] using congrArg BinaryTree.right hval
      · intro i hi
        exact (update_below σ d i _ hi).trans (hframe i hi)
  | pair a c iha ihc =>
      have ha : b + a.slots ≤ k := by simp only [slots] at hb; omega
      have hc : b + 1 + c.slots ≤ k := by simp only [slots] at hb; omega
      let d : Fin k := ⟨b, by have := a.slots_pos; omega⟩
      let d' : Fin k := ⟨b + 1, by have := c.slots_pos; omega⟩
      obtain ⟨n, σ, hrun, hval, hframe⟩ := iha b ha hv hzv ρ hz
      obtain ⟨m, τ, hrun', hval', hframe'⟩ := ihc (b + 1) hc
        (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv) σ
        ((hframe z hzv).trans hz)
      have hvars : σ ∘ v = ρ ∘ v := funext fun x ↦ hframe (v x) (hv x)
      refine ⟨n + (m + 1), (TreeMachine.Op.pair d d d').eval τ,
        hrun.bind (hrun'.bind (TreeMachine.Program.exec_act _ _)), ?_, ?_⟩
      · have hd : τ d = a.eval (ρ ∘ v) :=
          (hframe' d (by dsimp [d]; omega)).trans hval
        simp [d, d', hd, hval', hvars]
      · intro i hi
        exact (update_below τ d i _ hi).trans
          ((hframe' i (by omega)).trans (hframe i hi))

end Complexity.TreeProgram.Expr
