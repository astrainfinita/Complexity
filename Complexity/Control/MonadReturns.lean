/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Multiset.Functor

/-!
# The values a computation can return

`returns x` is the set of values that the computation `x : m α` can return. A fact about every
result of `x` is stated as `∀ a ∈ returns x, P a`, for every monad with `MonadReturns`.

The laws say that `returns` is a morphism of monads into sets, and that a computation depends on
its continuation only at the values it can return. On `Id` the set is the singleton of the result;
on `Multiset` it is the set of members, forgetting multiplicities.

These are the laws proved for each monad in Isabelle/HOL (`set_return_pmf`, `set_bind_pmf`,
`bind_pmf_cong`). In the terms of Manes, a monad with such a set is a principal taut monad, and a
collection monad when the sets are finite. Core's `MonadAttach.CanReturn` is the same predicate,
with laws that serve termination proofs.

Current state: a lemma stated with `returns` applies to a plain statement about the members of a
multiset by definition, but the unifier unfolds the membership of `Multiset` before it unfolds
`returns`, which costs elaboration time at each such use.
-/

@[expose] public section

universe u v

namespace Complexity

/-- A monad whose computations have a set of values they can return. -/
class MonadReturns (m : Type u → Type v) [Monad m] where
  /-- The values a computation can return. -/
  returns {α : Type u} : m α → Set α
  /-- `pure a` can return only `a`. -/
  mem_returns_pure_iff {α : Type u} {a b : α} : b ∈ returns (pure a : m α) ↔ b = a
  /-- `x >>= f` can return what `f a` can return, for the values `a` that `x` can return. -/
  mem_returns_bind_iff {α β : Type u} {x : m α} {f : α → m β} {b : β} :
    b ∈ returns (x >>= f) ↔ ∃ a ∈ returns x, b ∈ returns (f a)
  /-- A computation depends on its continuation only at the values it can return. -/
  bind_congr {α β : Type u} {x : m α} {f g : α → m β} :
    (∀ a ∈ returns x, f a = g a) → x >>= f = x >>= g

export MonadReturns (returns mem_returns_pure_iff mem_returns_bind_iff)

variable {m : Type u → Type v} [Monad m] [MonadReturns m] {α β : Type u}

theorem mem_returns_map_iff [LawfulMonad m] {f : α → β} {x : m α} {b : β} :
    b ∈ returns (f <$> x) ↔ ∃ a ∈ returns x, f a = b := by
  simp only [← bind_pure_comp, mem_returns_bind_iff, mem_returns_pure_iff, eq_comm]

instance : MonadReturns Id where
  returns x := {x.run}
  mem_returns_pure_iff := Iff.rfl
  mem_returns_bind_iff {_ _ x _ _} :=
    ⟨fun h ↦ ⟨x.run, rfl, h⟩, fun ⟨_, ha, h⟩ ↦ by subst ha; exact h⟩
  bind_congr h := h _ rfl

/-- A deterministic computation can return exactly its result. -/
@[simp] theorem _root_.Id.mem_returns {x : Id α} {a : α} : a ∈ returns x ↔ a = x.run := Iff.rfl

instance : MonadReturns Multiset where
  returns s := {a | a ∈ s}
  mem_returns_pure_iff := Multiset.mem_singleton
  mem_returns_bind_iff := Multiset.mem_bind
  bind_congr := Multiset.bind_congr

/-- A multiset of branches can return exactly its members. -/
@[simp] theorem _root_.Multiset.mem_returns {s : Multiset α} {a : α} : a ∈ returns s ↔ a ∈ s :=
  Iff.rfl

end Complexity
