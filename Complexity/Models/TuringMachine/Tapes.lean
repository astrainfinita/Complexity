/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Configuration
public import Complexity.Data.Embedding
public import Mathlib.Data.Fin.Embedding

/-! # Adding work tapes

A work layout selects the source tapes. Unassigned tapes are left untouched; the existing
`liftWork` and `restrictWork` interfaces use the prefix layout.
-/

@[expose] public section

namespace Complexity.TM

variable {k l : ℕ} {Γ Q : Type*}

section Layout

variable {κ τ : Type*}

section Restrict

variable [Inhabited Γ] {xs : Array Γ}

/-- Keep the tapes selected by a layout, without changing input, output, or control. -/
@[simps]
def Cfg.restrictWorkAlong (L : κ ↪ τ) (c : Cfg τ Γ Q xs) : Cfg κ Γ Q xs where
  state := c.state
  inputPos := c.inputPos
  workTapes := c.workTapes ∘ L
  workPos := c.workPos ∘ L
  output := c.output

/-- Restricting through two banks agrees with the composed layout. -/
theorem Cfg.restrictWorkAlong_comp {σ : Type*} (L : κ ↪ τ) (M : τ ↪ σ)
    (c : Cfg σ Γ Q xs) :
    (c.restrictWorkAlong M).restrictWorkAlong L = c.restrictWorkAlong (L.trans M) := rfl

end Restrict

variable [Fintype κ] [DecidableEq τ]

/-- Extend an action along a layout, leaving every unassigned tape idle. -/
@[simps]
def Action.liftWorkAlong (L : κ ↪ τ) (a : Action κ Γ Q) : Action τ Γ Q where
  inputMove := a.inputMove
  work := L.replace a.work (fun _ ↦ (none, 0))
  output := a.output
  state := a.state

/-- Lifting actions through two banks agrees with the composed layout. -/
theorem Action.liftWorkAlong_comp {σ : Type*} [Fintype τ] [DecidableEq σ] (L : κ ↪ τ) (M : τ ↪ σ)
    (a : Action κ Γ Q) : (a.liftWorkAlong L).liftWorkAlong M = a.liftWorkAlong (L.trans M) := by
  simp only [liftWorkAlong]
  congr 1
  exact L.replace_comp M a.work (fun _ ↦ (none, 0))

variable [Inhabited Γ] {xs : Array Γ}

/-- Install a local result in its caller, preserving work tapes and heads outside the layout.
The local computation supplies the shared input position, output, and control state. -/
@[simps]
def Cfg.replaceWorkAlong (L : κ ↪ τ) (source : Cfg κ Γ Q xs)
    (target : Cfg τ Γ Q xs) : Cfg τ Γ Q xs where
  state := source.state
  inputPos := source.inputPos
  workTapes := L.replace source.workTapes target.workTapes
  workPos := L.replace source.workPos target.workPos
  output := source.output

@[simp] theorem Cfg.restrictWorkAlong_replaceWorkAlong (L : κ ↪ τ)
    (source : Cfg κ Γ Q xs) (target : Cfg τ Γ Q xs) :
    (Cfg.replaceWorkAlong L source target).restrictWorkAlong L = source := by
  cases source
  simp [replaceWorkAlong, restrictWorkAlong]

@[simp] theorem Cfg.replaceWorkAlong_restrictWorkAlong (L : κ ↪ τ)
    (c : Cfg τ Γ Q xs) : Cfg.replaceWorkAlong L (c.restrictWorkAlong L) c = c := by
  cases c
  simp [replaceWorkAlong, restrictWorkAlong]

/-- Sequential local results share the same untouched caller state. -/
@[simp] theorem Cfg.replaceWorkAlong_replaceWorkAlong (L : κ ↪ τ)
    (source next : Cfg κ Γ Q xs) (target : Cfg τ Γ Q xs) :
    Cfg.replaceWorkAlong L next (Cfg.replaceWorkAlong L source target) =
      Cfg.replaceWorkAlong L next target := by
  simp only [replaceWorkAlong, Function.Embedding.replace_replace]

/-- Installing nested local results agrees with installing along the composed layout. -/
theorem Cfg.replaceWorkAlong_comp {σ : Type*} [Fintype τ] [DecidableEq σ] (L : κ ↪ τ) (M : τ ↪ σ)
    (source : Cfg κ Γ Q xs) (target : Cfg σ Γ Q xs) :
    Cfg.replaceWorkAlong M (Cfg.replaceWorkAlong L source (target.restrictWorkAlong M))
      target = Cfg.replaceWorkAlong (L.trans M) source target := by
  simp only [replaceWorkAlong, restrictWorkAlong, Function.Embedding.replace_comp]

/-- A lifted action updates only the installed local configuration. -/
theorem Action.apply_liftWorkAlong_replaceWorkAlong (L : κ ↪ τ)
    (a : Action κ Γ Q) (source : Cfg κ Γ Q xs) (target : Cfg τ Γ Q xs) :
    apply (a.liftWorkAlong L) (Cfg.replaceWorkAlong L source target) =
      Cfg.replaceWorkAlong L (apply a source) target := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j ∈ Set.range L
    · obtain ⟨i, rfl⟩ := hj
      simp
    · simp [hj]
  · funext j
    by_cases hj : j ∈ Set.range L
    · obtain ⟨i, rfl⟩ := hj
      simp
    · simp [hj]
  · rfl

@[simp] theorem Action.apply_liftWorkAlong_restrictWorkAlong (L : κ ↪ τ)
    (a : Action κ Γ Q) (c : Cfg τ Γ Q xs) :
    (apply (a.liftWorkAlong L) c).restrictWorkAlong L =
      apply a (c.restrictWorkAlong L) := by
  ext <;> simp

end Layout

section Prefix

/-- Extend a local action with idle work tapes after its original prefix. -/
def Action.liftWork (h : k ≤ l) (a : Action (Fin k) Γ Q) : Action (Fin l) Γ Q :=
  a.liftWorkAlong (Fin.castLEEmb h)

@[simp]
theorem Action.work_liftWork_castLE (h : k ≤ l) (a : Action (Fin k) Γ Q) (j : Fin k) :
    (a.liftWork h).work (Fin.castLE h j) = a.work j :=
  (Fin.castLEEmb h).replace_apply a.work (fun _ ↦ (none, 0)) j

@[simp]
theorem Action.work_liftWork_extra (h : k ≤ l) (a : Action (Fin k) Γ Q)
    (j : Fin l) (hj : k ≤ j.val) :
    (a.liftWork h).work j = (none, 0) := by
  apply (Fin.castLEEmb h).replace_of_not_mem
  rintro ⟨i, rfl⟩
  exact (Nat.not_lt_of_ge hj) i.isLt

variable [Inhabited Γ] {xs : Array Γ}

/-- Keep the first `k` work tapes, without changing input, output, or control. -/
def Cfg.restrictWork (h : k ≤ l) (c : Cfg (Fin l) Γ Q xs) : Cfg (Fin k) Γ Q xs :=
  c.restrictWorkAlong (Fin.castLEEmb h)

@[simp]
theorem Action.apply_liftWork_restrictWork (h : k ≤ l) (a : Action (Fin k) Γ Q)
    (c : Cfg (Fin l) Γ Q xs) :
    (apply (a.liftWork h) c).restrictWork h =
      apply a (c.restrictWork h) :=
  a.apply_liftWorkAlong_restrictWorkAlong (Fin.castLEEmb h) c

end Prefix

end Complexity.TM
