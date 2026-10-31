/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Models.TreeMachine.Program.Resources

/-! # Compiling tree expressions with reusable temporary registers -/

@[expose] public section

namespace Complexity.TreeProgram.Expr

open Controller (History)

variable {ν : Type} {k : ℕ}

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

/-- Compilation preserves the value and exact time, bounding each register peak by the
previous peak and the largest source tree encountered during evaluation. -/
theorem exec_compile_history (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hz : s.last.regs z = .nil) :
    ∃ t i, (e.compile v z b hb).Exec TreeMachine.Program.historySemantics s e.steps i t ∧
      t.last.regs i = e.eval (s.last.regs ∘ v) ∧ i.val ≤ b ∧
      (∀ j : Fin k, j.val < b → t.last.regs j = s.last.regs j) ∧
      ∀ j, t.configSup (fun c ↦ (c.regs j).size) ≤
        s.configSup (fun c ↦ (c.regs j).size) ⊔ e.maxSize (s.last.regs ∘ v) := by
  induction e generalizing b s with
  | nil => exact ⟨s, z, Program.Exec.pure _ _ _, hz, hzv.le, fun _ _ ↦ rfl,
      fun _ ↦ le_sup_left⟩
  | var x => exact ⟨s, v x, Program.Exec.pure _ _ _, rfl, (hv x).le, fun _ _ ↦ rfl,
      fun _ ↦ le_sup_left⟩
  | left e ih | right e ih =>
      obtain ⟨t, i, hr, hval, _, hf, hpeak⟩ := ih b
        (by simp only [slots] at hb; omega) hv hzv s hz
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨t.snoc _, d, hr.bind ((TreeMachine.Program.exec_act_history _ t).bind
        (f := fun _ ↦ pure d) (Program.Exec.pure _ d _)), ?_, le_rfl, ?_, ?_⟩
      · simp [d, hval]
      · intro j hj
        have hd : j ≠ d := by intro h; subst j; exact (lt_irrefl b) hj
        simpa [d, hd] using hf j hj
      · intro j
        apply (TreeMachine.configSup_reg_size_snoc_le t _ j).trans
        apply max_le (hpeak j)
        apply le_sup_of_le_right
        simpa [TreeMachine.Action.sizeCost, hval] using
          e.size_eval_le_maxSize (s.last.regs ∘ v)
  | pair a c iha ihc =>
      obtain ⟨t, i, hr, hval, hi, hf, hpeak⟩ := iha b
        (by simp only [slots] at hb; omega) hv hzv s hz
      obtain ⟨u, j, hr', hval', _, hf', hpeak'⟩ := ihc (b + 1)
        (by simp only [slots] at hb; omega)
        (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv) t
        ((hf z hzv).trans hz)
      have hvars : t.last.regs ∘ v = s.last.regs ∘ v := funext fun x ↦ hf (v x) (hv x)
      let d : Fin k := ⟨b, by simp only [slots] at hb; omega⟩
      refine ⟨u.snoc (.pair d i j), d, ?_, ?_, le_rfl, ?_, ?_⟩
      · exact hr.bind (hr'.bind ((TreeMachine.Program.exec_act_history (.pair d i j) u).bind
          (f := fun _ ↦ pure d) (Program.Exec.pure _ d _)))
      · simp [hf' i (by omega), hval, hval', hvars]
      · intro l hl
        have hd : l ≠ d := by intro h; subst l; exact (lt_irrefl b) hl
        simpa [hd] using (hf' l (by omega)).trans (hf l hl)
      · intro l
        have hp : u.configSup (fun c ↦ (c.regs l).size) ≤
            s.configSup (fun c ↦ (c.regs l).size) ⊔ (a.pair c).maxSize (s.last.regs ∘ v) := by
          have ha := hpeak l
          have hc := hpeak' l
          rw [hvars] at hc
          simp only [maxSize]
          omega
        apply (TreeMachine.configSup_reg_size_snoc_le u _ l).trans
        apply max_le hp
        apply le_sup_of_le_right
        simp [TreeMachine.Action.sizeCost,
          hf' i (by omega), hval, hval', hvars]

/-- The value-only conclusion follows by forgetting the execution history. -/
theorem exec_compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ σ i, (e.compile v z b hb).Exec TreeMachine.Program.semantics ρ e.steps i σ ∧
      σ i = e.eval (ρ ∘ v) ∧ i.val ≤ b ∧
      ∀ j : Fin k, j.val < b → σ j = ρ j := by
  obtain ⟨t, i, ht, hval, hi, hf, _⟩ := e.exec_compile_history v z b hb hv hzv
    (History.nil ⟨ρ⟩) hz
  exact ⟨t.last.regs, i, ht.map (fun h ↦ h.last.regs) (fun _ ↦ rfl)
    (by intro a h; ext i; simp), hval, hi, hf⟩

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

/-- Direct assignment preserves other source variables and bounds all intermediate register
values. The extra two nodes cover the temporary pair in the variable-copy macro. -/
theorem exec_assign_history (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hz : s.last.regs z = .nil) :
    ∃ t, (e.assign d v z b hb).Exec TreeMachine.Program.historySemantics s e.assignSteps () t ∧
      (∀ i : Fin k, i.val < b →
        t.last.regs i = Function.update s.last.regs d (e.eval (s.last.regs ∘ v)) i) ∧
      ∀ i, t.configSup (fun c ↦ (c.regs i).size) ≤
        s.configSup (fun c ↦ (c.regs i).size) ⊔ (e.maxSize (s.last.regs ∘ v) + 2) := by
  cases e with
  | nil =>
      refine ⟨_, TreeMachine.Program.exec_act_history _ _, ?_, ?_⟩
      · intro i _
        simp [hz]
      · intro i
        have hi := s.config_le_configSup (fun c ↦ (c.regs i).size) s.last_mem_configs
        by_cases hd : i = d <;> simp [hd, hz, maxSize] <;> omega
  | var x =>
      let u := s.snoc (.pair d (v x) z)
      refine ⟨u.snoc (.left d d),
        (TreeMachine.Program.exec_act_history (.pair d (v x) z) s).bind
          (f := fun _ ↦ TreeMachine.Program.act (.left d d))
          (TreeMachine.Program.exec_act_history (.left d d) u), ?_, ?_⟩
      · intro i _
        simp [u]
      · intro i
        have hi := s.config_le_configSup (fun c ↦ (c.regs i).size) s.last_mem_configs
        by_cases hd : i = d <;> simp [u, hd, hz, maxSize, Tree.size_pair] <;> omega
  | left e | right e =>
      obtain ⟨t, j, hr, hval, _, hf, hpeak⟩ := e.exec_compile_history v z b
        (by simp only [slots] at hb; omega) hv hzv s hz
      refine ⟨_, hr.bind (TreeMachine.Program.exec_act_history _ _), ?_, ?_⟩
      · intro i hi
        by_cases h : i = d <;> simp [h, hval, hf i hi]
      · intro i
        apply (TreeMachine.configSup_reg_size_snoc_le t _ i).trans
        apply max_le ((hpeak i).trans (max_le_max_left _ (Nat.le_add_right _ 2)))
        apply le_sup_of_le_right
        simpa [TreeMachine.Action.sizeCost, hval] using
          (e.size_eval_le_maxSize (s.last.regs ∘ v)).trans (Nat.le_add_right _ 2)
  | pair a c =>
      obtain ⟨t, i, hr, hval, hi, hf, hpeak⟩ := a.exec_compile_history v z b
        (by simp only [slots] at hb; omega) hv hzv s hz
      obtain ⟨u, j, hr', hval', _, hf', hpeak'⟩ := c.exec_compile_history v z (b + 1)
        (by simp only [slots] at hb; omega)
        (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv) t
        ((hf z hzv).trans hz)
      have hvars : t.last.regs ∘ v = s.last.regs ∘ v := funext fun x ↦ hf (v x) (hv x)
      refine ⟨_, hr.bind (hr'.bind (TreeMachine.Program.exec_act_history _ _)), ?_, ?_⟩
      · intro l hl
        by_cases h : l = d
        · simp [h, hf' i (by omega), hval, hval', hvars]
        · simp [h, hf' l (by omega), hf l hl]
      · intro l
        have hp : u.configSup (fun c ↦ (c.regs l).size) ≤
            s.configSup (fun c ↦ (c.regs l).size) ⊔
              ((a.pair c).maxSize (s.last.regs ∘ v) + 2) := by
          have ha := hpeak l
          have hc := hpeak' l
          rw [hvars] at hc
          simp only [maxSize]
          omega
        apply (TreeMachine.configSup_reg_size_snoc_le u _ l).trans
        apply max_le hp
        apply le_sup_of_le_right
        simpa [TreeMachine.Action.sizeCost,
          hf' i (by omega), hval, hval', hvars] using
          (size_eval_le_maxSize (.pair a c) (s.last.regs ∘ v)).trans (Nat.le_add_right _ 2)

/-- Assignment preserves every other source variable, including when a source aliases `d`. -/
theorem exec_assign (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ σ, (e.assign d v z b hb).Exec TreeMachine.Program.semantics ρ e.assignSteps () σ ∧
      ∀ i : Fin k, i.val < b → σ i = Function.update ρ d (e.eval (ρ ∘ v)) i := by
  obtain ⟨t, ht, hf, _⟩ := e.exec_assign_history d v z b hb hv hzv (History.nil ⟨ρ⟩) hz
  exact ⟨t.last.regs, ht.map (fun h ↦ h.last.regs) (fun _ ↦ rfl)
    (by intro a h; ext i; simp), hf⟩

end Complexity.TreeProgram.Expr
