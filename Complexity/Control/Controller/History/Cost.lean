/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.History
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-! # Resource statistics of finite histories -/

@[expose] public section

namespace Complexity.Controller.History

variable {Config Action : Type*} [Apply Config Action]

/-- Sum action charges at their source configurations. -/
def actionSum (h : History Config Action) (cost : Action → Config → ℕ) : ℕ :=
  ((h.actions.zip h.configs).map fun (a, c) ↦ cost a c).sum

/-- Supremum of configuration charges, including both endpoints. -/
def configSup {α : Type*} [SemilatticeSup α] (h : History Config Action)
    (space : Config → α) : α :=
  h.configs.tail.foldl (fun b c ↦ b ⊔ space c) (space h.first)

theorem configSup_le_iff {α : Type*} [SemilatticeSup α]
    (h : History Config Action) (space : Config → α) (b : α) :
    h.configSup space ≤ b ↔ ∀ c ∈ h.configs, space c ≤ b := by
  have hf (l : List Config) (a : α) :
      l.foldl (fun b c ↦ b ⊔ space c) a ≤ b ↔ a ≤ b ∧ ∀ c ∈ l, space c ≤ b := by
    induction l generalizing a <;> simp_all [sup_le_iff, and_assoc]
  rw [configSup, hf]
  conv_rhs => rw [← List.cons_head_tail h.configs_ne_nil]
  simp

theorem config_le_configSup {α : Type*} [SemilatticeSup α]
    (h : History Config Action) (space : Config → α) {c : Config}
    (hc : c ∈ h.configs) : space c ≤ h.configSup space :=
  (h.configSup_le_iff space _).1 le_rfl c hc

@[simp] theorem actionSum_nil (c : Config) (cost : Action → Config → ℕ) :
    (nil c).actionSum cost = 0 := by
  simp [actionSum]

@[simp] theorem configSup_nil {α : Type*} [SemilatticeSup α]
    (c : Config) (space : Config → α) :
    (nil (Action := Action) c).configSup space = space c := by
  simp [configSup]

@[simp] theorem actionSum_const (h : History Config Action) (k : ℕ) :
    h.actionSum (fun _ _ ↦ k) = h.length * k := by
  simp [actionSum, length]

theorem actionSum_unit (h : History Config Action) :
    h.actionSum (fun _ _ ↦ 1) = h.length := by
  simp only [actionSum_const, Nat.mul_one]

theorem actionSum_mono (h : History Config Action) {cost cost' : Action → Config → ℕ}
    (hc : ∀ a c, (a, c) ∈ h.actions.zip h.configs → cost a c ≤ cost' a c) :
    h.actionSum cost ≤ h.actionSum cost' :=
  List.sum_le_sum fun ⟨a, c⟩ hm ↦ hc a c hm

@[simp] theorem actionSum_cons (c : Config) (a : Action) (h : History Config Action)
    (he : h.first = apply a c) (cost : Action → Config → ℕ) :
    (cons c a h he).actionSum cost = cost a c + h.actionSum cost := by
  simp [actionSum]

@[simp] theorem configSup_cons {α : Type*} [SemilatticeSup α]
    (c : Config) (a : Action) (h : History Config Action)
    (he : h.first = apply a c) (space : Config → α) :
    (cons c a h he).configSup space = space c ⊔ h.configSup space := by
  apply eq_of_forall_ge_iff
  intro b
  simp only [configSup_le_iff, configs_cons, List.mem_cons, forall_eq_or_imp,
    sup_le_iff]

/-- Local action bounds control the peak potential throughout a history. -/
theorem configSup_le_add_actionSum (h : History Config Action) (potential : Config → ℕ)
    (cost : Action → Config → ℕ)
    (hs : ∀ a c, (a, c) ∈ h.actions.zip h.configs →
      potential (apply a c) ≤ potential c + cost a c) :
    h.configSup potential ≤ potential h.first + h.actionSum cost := by
  rcases h with ⟨c, as⟩
  induction as generalizing c with
  | nil => simp [configSup, configs, actionSum]
  | cons a as ih =>
    simp [configs, or_imp, forall_and] at hs
    apply (configSup_cons c a ⟨apply a c, as⟩ rfl potential).trans_le
    apply sup_le (Nat.le_add_right _ _)
    simpa [actionSum, configs, Nat.add_assoc] using
      (ih (apply a c) hs.2).trans (Nat.add_le_add_right hs.1 _)

@[simp] theorem actionSum_append (p q : History Config Action) (h : p.last = q.first)
    (cost : Action → Config → ℕ) :
    (p.append q h).actionSum cost = p.actionSum cost + q.actionSum cost := by
  rcases p with ⟨c, as⟩
  induction as generalizing c with
  | nil => simp [actionSum, append, configs, ← h, last]
  | cons a as ih =>
    simpa [actionSum, append, configs, Nat.add_assoc] using
      congrArg (cost a c + ·) (ih (apply a c) h)

@[simp] theorem configSup_append {α : Type*} [SemilatticeSup α]
    (p q : History Config Action) (h : p.last = q.first) (space : Config → α) :
    (p.append q h).configSup space = p.configSup space ⊔ q.configSup space := by
  apply eq_of_forall_ge_iff
  intro b
  simp only [configSup_le_iff, mem_configs_append, or_imp, forall_and, sup_le_iff]

@[simp] theorem configSup_snoc {α : Type*} [SemilatticeSup α]
    (p : History Config Action) (a : Action) (space : Config → α) :
    (p.snoc a).configSup space = p.configSup space ⊔ space (apply a p.last) := by
  simp [configSup, configs_snoc, configs_ne_nil, List.foldl_append]

@[simp] theorem configSup_apply {ι α : Type*} [SemilatticeSup α]
    (p : History Config Action) (space : Config → ι → α) (i : ι) :
    p.configSup space i = p.configSup (fun c ↦ space c i) :=
  (List.foldl_hom (fun f : ι → α ↦ f i) (fun _ _ ↦ rfl)).symm

@[simp] theorem configSup_map {Config' Action' α : Type*}
    [Apply Config' Action'] [SemilatticeSup α] (p : History Config Action)
    (f : Config → Config') (g : Action → Action')
    (h : ∀ a c, f (apply a c) = apply (g a) (f c)) (space : Config' → α) :
    (p.map f g).configSup space = p.configSup (space ∘ f) := by
  simp [configSup, configs_map _ _ _ h, ← List.map_tail, List.foldl_map]

end Complexity.Controller.History
