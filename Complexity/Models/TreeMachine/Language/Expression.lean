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

/-- Exact unit time for obtaining an expression's value; existing values need no copy. -/
def steps : Expr ν → ℕ
  | .nil | .var _ => 0
  | .left e | .right e => e.steps + 1
  | .pair a b => a.steps + (b.steps + 1)

/-- Temporary registers for evaluating an expression, excluding its source variables. -/
def slots : Expr ν → ℕ
  | .nil | .var _ => 0
  | .left e | .right e => max 1 e.slots
  | .pair a b => max a.slots (b.slots + 1)

/-- Return the register containing the value. Atoms use their existing registers;
compound expressions use `b`, preserving the source layout below it. -/
def compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program k (Fin k) :=
  match e with
  | .nil => pure z
  | .var x => pure (v x)
  | .left e => do
      let i ← e.compile v z b (by simp only [slots] at hb; omega)
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      TreeMachine.Program.act (.left d i)
      pure d
  | .right e => do
      let i ← e.compile v z b (by simp only [slots] at hb; omega)
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      TreeMachine.Program.act (.right d i)
      pure d
  | .pair a c => do
      let i ← a.compile v z b (by simp only [slots] at hb; omega)
      let j ← c.compile v z (b + 1) (by simp only [slots] at hb; omega)
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      TreeMachine.Program.act (.pair d i j)
      pure d

private theorem update_below (ρ : Fin k → Tree) (d i : Fin k) (x : Tree)
    (hi : i.val < d.val) : Function.update ρ d x i = ρ i := by
  have h : i ≠ d := by intro h; subst i; omega
  simp [h]

/-- Compilation takes the exact static number of steps and returns a register at or below `b`. -/
theorem exec_compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ σ i, (e.compile v z b hb).Exec TreeMachine.Program.semantics ρ e.steps i σ ∧
      σ i = e.eval (ρ ∘ v) ∧ i.val ≤ b ∧
      ∀ j : Fin k, j.val < b → σ j = ρ j := by
  induction e generalizing b ρ with
  | nil => exact ⟨ρ, z, Program.Exec.pure _ _ _, hz, hzv.le, fun _ _ ↦ rfl⟩
  | var x => exact ⟨ρ, v x, Program.Exec.pure _ _ _, rfl, (hv x).le, fun _ _ ↦ rfl⟩
  | left e ih | right e ih =>
      obtain ⟨σ, i, hr, hval, _, hf⟩ := ih b (by simp only [slots] at hb; omega) hv hzv ρ hz
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨_, d, hr.bind ((TreeMachine.Program.exec_act _ σ).bind
        (f := fun _ ↦ pure d) (Program.Exec.pure _ d _)), ?_, le_rfl, ?_⟩
      · simp [d, hval]
      · intro j hj
        exact (update_below σ d j _ hj).trans (hf j hj)
  | pair a c iha ihc =>
      obtain ⟨σ, i, hr, hval, hi, hf⟩ := iha b
        (by simp only [slots] at hb; omega) hv hzv ρ hz
      obtain ⟨τ, j, hr', hval', _, hf'⟩ := ihc (b + 1)
        (by simp only [slots] at hb; omega)
        (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv) σ
        ((hf z hzv).trans hz)
      have hvars : σ ∘ v = ρ ∘ v := funext fun x ↦ hf (v x) (hv x)
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨(TreeMachine.Op.pair d i j).eval τ, d, ?_, ?_, le_rfl, ?_⟩
      · exact hr.bind (hr'.bind
          ((TreeMachine.Program.exec_act (.pair d i j) τ).mapResult (w := .value) fun _ ↦ d))
      · simp [hf' i (by omega), hval, hval', hvars]
      · intro j hj
        exact (update_below τ d j _ hj).trans ((hf' j (by omega)).trans (hf j hj))

/-- Assignments write their final operation directly to the destination.
Only assigning an existing variable needs the two-instruction copy macro. -/
def assign (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program k Unit :=
  match e with
  | .nil => TreeMachine.Program.act (.left d z)
  | .var x => TreeMachine.Program.copy z d (v x)
  | .left e => do
      let i ← e.compile v z b (by simp only [slots] at hb; omega)
      TreeMachine.Program.act (.left d i)
  | .right e => do
      let i ← e.compile v z b (by simp only [slots] at hb; omega)
      TreeMachine.Program.act (.right d i)
  | .pair a c => do
      let i ← a.compile v z b (by simp only [slots] at hb; omega)
      let j ← c.compile v z (b + 1) (by simp only [slots] at hb; omega)
      TreeMachine.Program.act (.pair d i j)

/-- Exact unit time when the expression is assigned to a source variable. -/
def assignSteps : Expr ν → ℕ
  | .nil => 1
  | .var _ => 2
  | e => e.steps

/-- Assignment preserves every other source variable, including when a source aliases `d`. -/
theorem exec_assign (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ σ, (e.assign d v z b hb).Exec TreeMachine.Program.semantics ρ e.assignSteps () σ ∧
      ∀ i : Fin k, i.val < b → σ i = Function.update ρ d (e.eval (ρ ∘ v)) i := by
  cases e with
  | nil =>
      refine ⟨_, TreeMachine.Program.exec_act _ _, ?_⟩
      intro i _
      simp [hz]
  | var x => exact ⟨_, TreeMachine.Program.exec_copy _ _ _ _, fun _ _ ↦ rfl⟩
  | left e | right e =>
      obtain ⟨σ, j, hr, hval, _, hf⟩ := e.exec_compile v z b
        (by simp only [slots] at hb; omega) hv hzv ρ hz
      refine ⟨_, hr.bind (TreeMachine.Program.exec_act _ _), ?_⟩
      intro i hi
      by_cases h : i = d <;> simp [h, hval, hf i hi]
  | pair a c =>
      obtain ⟨σ, i, hr, hval, hi, hf⟩ := a.exec_compile v z b
        (by simp only [slots] at hb; omega) hv hzv ρ hz
      obtain ⟨τ, j, hr', hval', _, hf'⟩ := c.exec_compile v z (b + 1)
        (by simp only [slots] at hb; omega)
        (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv) σ
        ((hf z hzv).trans hz)
      have hvars : σ ∘ v = ρ ∘ v := funext fun x ↦ hf (v x) (hv x)
      refine ⟨_, hr.bind (hr'.bind (TreeMachine.Program.exec_act _ _)), ?_⟩
      intro l hl
      by_cases h : l = d
      · simp [h, hf' i (by omega), hval, hval', hvars]
      · simp [h, hf' l (by omega), hf l hl]

end Complexity.TreeProgram.Expr
