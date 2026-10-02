/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel
public import Mathlib.Data.Multiset.Basic

/-!
# Nondeterministic decision bounds

A behavior supplies the complete multiset of branch outputs within joint resource
bounds. Every output must decode as a Boolean; acceptance means some output decodes
as `true`. Invalid input codes impose no obligations.
-/

@[expose] public section

namespace Complexity.TimeSpaceModel

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]

/-- One behavior decides a predicate on every valid input code within both bounds.
All branch outputs are Boolean codes, and acceptance is existential. -/
def NDecidableInTimeAndSpace (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t s : ℕ → ℕ) : Prop :=
  ∃ R ∈ model.behaviors, ∀ x a, a ∈ decode α x →
    ∃ ys, R x ys (t (model.inputSize x)) (s (model.inputSize x)) ∧
      (∀ y ∈ ys, (decode Bool y).Dom) ∧
      ((∃ y ∈ ys, true ∈ decode Bool y) ↔ p a)

/-- Decide a predicate nondeterministically within a pointwise time bound. -/
def NDecidableInTime (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t : ℕ → ℕ) : Prop :=
  ∃ s, model.NDecidableInTimeAndSpace p t s

/-- Decide a predicate nondeterministically within a pointwise space bound,
with some time bound requiring every branch to terminate. -/
def NDecidableInSpace (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (s : ℕ → ℕ) : Prop :=
  ∃ t, model.NDecidableInTimeAndSpace p t s

variable {model : TimeSpaceModel Multiset Data} {p q : α → Prop}
  {t s t' s' : ℕ → ℕ}

theorem NDecidableInTimeAndSpace.mono (h : model.NDecidableInTimeAndSpace p t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    model.NDecidableInTimeAndSpace p t' s' := by
  obtain ⟨R, hR, h⟩ := h
  refine ⟨R, hR, fun x a ha => ?_⟩
  obtain ⟨ys, hy, hb, hp⟩ := h x a ha
  exact ⟨ys, model.budget_mono hR hy (ht _) (hs _), hb, hp⟩

theorem NDecidableInTimeAndSpace.congr (h : model.NDecidableInTimeAndSpace p t s)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableInTimeAndSpace q t s :=
  funext (fun a => propext (hp a)) ▸ h

theorem NDecidableInTimeAndSpace.ndecidableInTime
    (h : model.NDecidableInTimeAndSpace p t s) : model.NDecidableInTime p t :=
  ⟨s, h⟩

theorem NDecidableInTimeAndSpace.ndecidableInSpace
    (h : model.NDecidableInTimeAndSpace p t s) : model.NDecidableInSpace p s :=
  ⟨t, h⟩

theorem NDecidableInTime.mono (h : model.NDecidableInTime p t)
    (ht : ∀ n, t n ≤ t' n) : model.NDecidableInTime p t' := by
  obtain ⟨s, h⟩ := h
  exact ⟨s, h.mono ht (fun _ => le_rfl)⟩

theorem NDecidableInTime.congr (h : model.NDecidableInTime p t)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableInTime q t :=
  funext (fun a => propext (hp a)) ▸ h

theorem NDecidableInSpace.mono (h : model.NDecidableInSpace p s)
    (hs : ∀ n, s n ≤ s' n) : model.NDecidableInSpace p s' := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.mono (fun _ => le_rfl) hs⟩

theorem NDecidableInSpace.congr (h : model.NDecidableInSpace p s)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableInSpace q s :=
  funext (fun a => propext (hp a)) ▸ h

end Complexity.TimeSpaceModel
