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
    (hb : b + e.slots ≤ k) : TreeMachine.Program Id k (Fin k) :=
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

/-- Compilation preserves the value within `e.steps` steps, bounding each register peak by the
previous peak and the largest source tree encountered during evaluation. -/
theorem execWithin_compile (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hv : ∀ x, (v x).val < b) (hzv : z.val < b) (hz : s.last.regs z = .nil) :
    (e.compile v z b hb).ExecWithin TreeMachine.Program.historySemantics s e.steps
      fun i t _ ↦ t.last.regs i = e.eval (s.last.regs ∘ v) ∧ i.val ≤ b ∧
        (∀ j : Fin k, j.val < b → t.last.regs j = s.last.regs j) ∧
        ∀ j, t.configSup (fun c ↦ (c.regs j).size) ≤
          s.configSup (fun c ↦ (c.regs j).size) ⊔ e.maxSize (s.last.regs ∘ v) := by
  induction e generalizing b s with
  | nil => exact .ret _ _ _ ⟨hz, hzv.le, fun _ _ ↦ rfl, fun _ ↦ le_sup_left⟩
  | var x => exact .ret _ _ _ ⟨rfl, (hv x).le, fun _ _ ↦ rfl, fun _ ↦ le_sup_left⟩
  | left e ih | right e ih =>
    refine (ih b _ s hv hzv hz).bindTo_add fun i t ⟨hval, _, hf, hpeak⟩ ↦
      TreeMachine.Program.execWithinWith_act_bind
        (.ret _ _ _ ⟨by simp [hval], le_rfl, fun j hj ↦ ?_, fun j ↦ ?_⟩)
    · simpa [Function.update_apply, Fin.ext_iff, hj.ne] using hf j hj
    · apply (TreeMachine.configSup_reg_size_snoc_le t _ j).trans
      apply max_le (hpeak j)
      apply le_sup_of_le_right
      simpa [TreeMachine.Action.sizeCost, hval] using
        e.size_eval_le_maxSize (s.last.regs ∘ v)
  | pair a c iha ihc =>
    refine (iha b _ s hv hzv hz).bindTo_add fun i t ⟨hval, hi, hf, hpeak⟩ ↦ ?_
    have hvars : t.last.regs ∘ v = s.last.regs ∘ v := funext fun x ↦ hf (v x) (hv x)
    refine (ihc (b + 1) _ t (fun x ↦ Nat.lt_succ_of_lt (hv x)) (Nat.lt_succ_of_lt hzv)
      ((hf z hzv).trans hz)).bindTo_add fun j u ⟨hval', _, hf', hpeak'⟩ ↦
        TreeMachine.Program.execWithinWith_act_bind
          (.ret _ _ _ ⟨?_, le_rfl, fun l hl ↦ ?_, fun l ↦ ?_⟩)
    · simp [hf' i (by omega), hval, hval', hvars]
    · simpa [Function.update_apply, Fin.ext_iff, hl.ne] using
        (hf' l (by omega)).trans (hf l hl)
    · have hp : u.configSup (fun c ↦ (c.regs l).size) ≤
          s.configSup (fun c ↦ (c.regs l).size) ⊔ (a.pair c).maxSize (s.last.regs ∘ v) := by
        have ha := hpeak l
        have hc := hpeak' l
        rw [hvars] at hc
        simp only [maxSize]
        omega
      apply (TreeMachine.configSup_reg_size_snoc_le u _ l).trans
      apply max_le hp
      apply le_sup_of_le_right
      simp [TreeMachine.Action.sizeCost, hf' i (by omega), hval, hval', hvars]

/-- Assignments write their final operation directly to the destination.
Only assigning an existing variable needs the two-instruction copy macro. -/
def assign (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program Id k Unit :=
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
theorem execWithin_assign (e : Expr ν) (d : Fin k) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hv : ∀ x, (v x).val < b) (hzv : z.val < b) (hz : s.last.regs z = .nil) :
    (e.assign d v z b hb).ExecWithin TreeMachine.Program.historySemantics s e.assignSteps
      fun _ t _ ↦ (∀ i : Fin k, i.val < b →
          t.last.regs i = Function.update s.last.regs d (e.eval (s.last.regs ∘ v)) i) ∧
        ∀ i, t.configSup (fun c ↦ (c.regs i).size) ≤
          s.configSup (fun c ↦ (c.regs i).size) ⊔ (e.maxSize (s.last.regs ∘ v) + 2) := by
  cases e with
  | nil =>
    refine TreeMachine.Program.execWithinWith_act ⟨fun i _ ↦ by simp [hz], fun i ↦ ?_⟩
    have hi := s.config_le_configSup (fun c ↦ (c.regs i).size) s.last_mem_configs
    by_cases hd : i = d <;> simp [hd, hz, maxSize] <;> omega
  | var x =>
    refine TreeMachine.Program.execWithinWith_act_bind
      (TreeMachine.Program.execWithinWith_act ⟨fun i _ ↦ by simp, fun i ↦ ?_⟩)
    have hi := s.config_le_configSup (fun c ↦ (c.regs i).size) s.last_mem_configs
    by_cases hd : i = d <;> simp [hd, hz, maxSize, Tree.size_pair] <;> omega
  | left e | right e =>
    refine (e.execWithin_compile v z b _ s hv hzv hz).bindTo_add fun j t ⟨hval, _, hf, hpeak⟩ ↦
      TreeMachine.Program.execWithinWith_act ⟨fun i hi ↦ ?_, fun i ↦ ?_⟩
    · by_cases h : i = d <;> simp [h, hval, hf i hi]
    · apply (TreeMachine.configSup_reg_size_snoc_le t _ i).trans
      apply max_le ((hpeak i).trans (max_le_max_left _ (Nat.le_add_right _ 2)))
      apply le_sup_of_le_right
      simpa [TreeMachine.Action.sizeCost, hval] using
        (e.size_eval_le_maxSize (s.last.regs ∘ v)).trans (Nat.le_add_right _ 2)
  | pair a c =>
    refine (a.execWithin_compile v z b _ s hv hzv hz).bindTo_add fun i t ⟨hval, hi, hf, hpeak⟩ ↦ ?_
    have hvars : t.last.regs ∘ v = s.last.regs ∘ v := funext fun x ↦ hf (v x) (hv x)
    refine (c.execWithin_compile v z (b + 1) _ t (fun x ↦ Nat.lt_succ_of_lt (hv x))
      (Nat.lt_succ_of_lt hzv) ((hf z hzv).trans hz)).bindTo_add fun j u ⟨hval', _, hf', hpeak'⟩ ↦
        TreeMachine.Program.execWithinWith_act ⟨fun l hl ↦ ?_, fun l ↦ ?_⟩
    · by_cases h : l = d
      · simp [h, hf' i (by omega), hval, hval', hvars]
      · simp [h, hf' l (by omega), hf l hl]
    · have hp : u.configSup (fun c ↦ (c.regs l).size) ≤
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
      simpa [TreeMachine.Action.sizeCost, hf' i (by omega), hval, hval', hvars] using
        (size_eval_le_maxSize (.pair a c) (s.last.regs ∘ v)).trans (Nat.le_add_right _ 2)

end Complexity.TreeProgram.Expr
