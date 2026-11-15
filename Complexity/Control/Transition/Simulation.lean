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
forms a pair with `Functor.Liftp`. On `Id` it is the relation
itself; on `Multiset` it is `Multiset.Rel`, which matches the branches one to one and retains
their multiplicities.

A relation that every step lifts is lifted by every finite iteration, for every monad. With
`MonadReturns`, every value one component can return is related to a value the other can return,
and facts about the values of the left component can be merged into the relation (`mono_of_mem`).
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

theorem LiftRel.swap {x : m α} {y : m β} (h : LiftRel R x y) : LiftRel (fun b a ↦ R a b) y x := by
  obtain ⟨z, rfl, rfl⟩ := h
  exact ⟨(fun p ↦ ⟨(p.1.2, p.1.1), p.2⟩) <$> z, by simp, by simp⟩

theorem LiftRel.map {f : α → γ} {g : β → δ} {x : m α} {y : m β} (h : LiftRel R x y)
    (hS : ∀ a b, R a b → S (f a) (g b)) : LiftRel S (f <$> x) (g <$> y) := by
  obtain ⟨z, rfl, rfl⟩ := h
  exact ⟨(fun p ↦ ⟨(f p.1.1, g p.1.2), hS _ _ p.2⟩) <$> z, by simp, by simp⟩

/-- A relation that is the graph of a function relates `x` only to its image. -/
theorem LiftRel.eq_map {x : m α} {y : m β} {f : α → β} (h : LiftRel R x y)
    (hR : ∀ a b, R a b → b = f a) : y = f <$> x := by
  obtain ⟨z, rfl, rfl⟩ := h
  rw [Functor.map_map]
  exact congrArg (· <$> z) (funext fun p ↦ hR _ _ p.2)

section Returns

variable [MonadReturns m]

/-- Weakening the relation where the left value can be returned. -/
theorem LiftRel.mono_of_mem {S : α → β → Prop} {x : m α} {y : m β} (h : LiftRel R x y)
    (hS : ∀ a ∈ returns x, ∀ b, R a b → S a b) : LiftRel S x y := by
  obtain ⟨z, rfl, rfl⟩ := h
  refine ⟨(fun q ↦ ⟨q.1.1, hS _ (mem_returns_map_iff.2 ⟨q.1, q.2, rfl⟩) _ q.1.2⟩) <$>
    MonadReturns.attach z, ?_, ?_⟩
  all_goals conv_rhs => rw [← MonadReturns.val_map_attach z]
  all_goals rw [Functor.map_map, Functor.map_map]

theorem LiftRel.exists_mem_of_mem_left {x : m α} {y : m β} (h : LiftRel R x y) {a : α}
    (ha : a ∈ returns x) : ∃ b ∈ returns y, R a b := by
  obtain ⟨z, rfl, rfl⟩ := h
  obtain ⟨p, hp, rfl⟩ := mem_returns_map_iff.1 ha
  exact ⟨p.1.2, mem_returns_map_iff.2 ⟨p, hp, rfl⟩, p.2⟩

theorem LiftRel.exists_mem_of_mem_right {x : m α} {y : m β} (h : LiftRel R x y) {b : β}
    (hb : b ∈ returns y) : ∃ a ∈ returns x, R a b := by
  obtain ⟨z, rfl, rfl⟩ := h
  obtain ⟨p, hp, rfl⟩ := mem_returns_map_iff.1 hb
  exact ⟨p.1.1, mem_returns_map_iff.2 ⟨p, hp, rfl⟩, p.2⟩

end Returns

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
