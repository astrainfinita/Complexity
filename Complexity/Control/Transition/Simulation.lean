/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Transition.Basic

/-!
# Simulation of monadic transitions

`LiftRel R x y` states that `x` and `y` are the two components of one computation whose results
are related by `R`. It is the version of mathlib's `Functor.Liftr` for two result types, and
forms a pair with `Functor.Liftp` (see `Transition.liftp_runN`). On `Id` it is the relation
itself; on `Multiset` it is `Multiset.Rel`, which matches the branches one to one and retains
their multiplicities.

A relation that every step lifts is lifted by every finite iteration, for every monad.
-/

@[expose] public section

universe u

namespace Complexity

variable {m : Type u → Type*} [Monad m] {α β γ δ : Type u}
  {R : α → β → Prop} {S : γ → δ → Prop}

/-- `x` and `y` are the two components of one computation whose results are related by `R`. -/
def LiftRel (R : α → β → Prop) (x : m α) (y : m β) : Prop :=
  ∃ z : m {p : α × β // R p.1 p.2}, (·.1.1) <$> z = x ∧ (·.1.2) <$> z = y

section Lawful

variable [LawfulMonad m]

theorem LiftRel.pure {a : α} {b : β} (h : R a b) : LiftRel R (pure a : m α) (pure b) :=
  ⟨Pure.pure ⟨(a, b), h⟩, by simp, by simp⟩

theorem LiftRel.bind {x : m α} {y : m β} {f : α → m γ} {g : β → m δ} (h : LiftRel R x y)
    (hfg : ∀ a b, R a b → LiftRel S (f a) (g b)) : LiftRel S (x >>= f) (y >>= g) := by
  obtain ⟨z, rfl, rfl⟩ := h
  choose v hv₁ hv₂ using hfg
  refine ⟨z >>= fun p ↦ v p.1.1 p.1.2 p.2, ?_, ?_⟩ <;>
    simp only [map_bind, bind_map_left, hv₁, hv₂]

/-- Two images of one computation are related when the two maps are, pointwise. -/
theorem LiftRel.map_map {R : β → γ → Prop} (x : m α) {f : α → β} {g : α → γ}
    (h : ∀ a, R (f a) (g a)) : LiftRel R (f <$> x) (g <$> x) :=
  ⟨(fun a ↦ ⟨(f a, g a), h a⟩) <$> x, by simp, by simp⟩

/-- A relation that every step lifts is lifted by every finite iteration. -/
theorem Transition.liftRel_runN {f : α → m α} {g : β → m β}
    (h : ∀ a b, R a b → LiftRel R (f a) (g b)) {a : α} {b : β} (hab : R a b) (n : ℕ) :
    LiftRel R (Transition.runN f n a) (Transition.runN g n b) := by
  induction n generalizing a b with
  | zero => exact .pure hab
  | succ n ih => exact (h a b hab).bind fun _ _ ↦ ih

end Lawful

theorem liftRel_id_iff {x : Id α} {y : Id β} : LiftRel R x y ↔ R x.run y.run :=
  ⟨by rintro ⟨z, rfl, rfl⟩; exact z.run.2, fun h ↦ ⟨Pure.pure ⟨(x.run, y.run), h⟩, rfl, rfl⟩⟩

/-- The deterministic reading of a lifted relation. Written `h.run`, it takes `R` from `h`, not
from the expected type. -/
alias ⟨LiftRel.run, _⟩ := liftRel_id_iff

theorem liftRel_multiset_iff {s : Multiset α} {t : Multiset β} :
    LiftRel R s t ↔ Multiset.Rel R s t := by
  constructor
  · rintro ⟨z, rfl, rfl⟩
    simp only [Multiset.fmap_def]
    exact Multiset.rel_map.mpr (Multiset.rel_refl_of_refl_on fun p _ ↦ p.2)
  · intro h
    induction h with
    | zero => exact ⟨0, rfl, rfl⟩
    | cons hab _ ih =>
      obtain ⟨z, rfl, rfl⟩ := ih
      exact ⟨⟨(_, _), hab⟩ ::ₘ z, by simp [Multiset.fmap_def], by simp [Multiset.fmap_def]⟩

/-- The branching reading of a lifted relation: the branches match one to one, with their
multiplicities. -/
alias ⟨LiftRel.multisetRel, _⟩ := liftRel_multiset_iff

end Complexity
