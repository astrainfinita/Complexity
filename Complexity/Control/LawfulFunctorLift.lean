/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# Lawful lifts of functors

A lift commutes with mapping results. This is the functor part of core's `LawfulMonadLift` and
`LawfulMonadLiftT`, for a source that is only a functor, such as a shape of choices. As there,
instances are declared for the one-step class `LawfulFunctorLift`, and definitions and lemmas
request `LawfulFunctorLiftT`, whose instances follow the chain of lifts.
-/

@[expose] public section

universe u

namespace Complexity

variable {m n o : Type u → Type*}

/-- The one-step lift `MonadLift n o` commutes with mapping results. Instances are declared for
this class, as for core's `LawfulMonadLift`; its source need only be a functor. -/
class LawfulFunctorLift (n : semiOutParam (Type u → Type*)) (o : Type u → Type*)
    [Functor n] [Functor o] [inst : MonadLift n o] : Prop where
  monadLift_map {α β : Type u} (f : α → β) (x : n α) :
    inst.monadLift (f <$> x) = f <$> inst.monadLift x

/-- The transitive lift `MonadLiftT m n` commutes with mapping results. Definitions and lemmas
request this class, as for core's `LawfulMonadLiftT`; its instances are obtained from
`LawfulFunctorLift` along the chain of lifts. -/
class LawfulFunctorLiftT (m : Type u → Type*) (n : Type u → Type*) [Functor m] [Functor n]
    [inst : MonadLiftT m n] : Prop where
  monadLift_map {α β : Type u} (f : α → β) (x : m α) :
    inst.monadLift (f <$> x) = f <$> inst.monadLift x

instance [Functor m] [Functor n] [Functor o] [MonadLift n o] [MonadLiftT m n]
    [LawfulFunctorLift n o] [LawfulFunctorLiftT m n] : LawfulFunctorLiftT m o where
  monadLift_map f x := (congrArg MonadLift.monadLift (LawfulFunctorLiftT.monadLift_map f x)).trans
    (LawfulFunctorLift.monadLift_map f _)

instance [Functor m] : LawfulFunctorLiftT m m where
  monadLift_map _ _ := rfl

/-- A lawful one-step lift of lawful monads is a lawful lift of functors. -/
instance [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [MonadLift n o]
    [LawfulMonadLift n o] : LawfulFunctorLift n o where
  monadLift_map f x := by
    rw [← bind_pure_comp, ← bind_pure_comp, LawfulMonadLift.monadLift_bind]
    simp only [LawfulMonadLift.monadLift_pure]

/-- The one-step lift `MonadLift n o` sends `Pure.pure a` to `pure a`. This is the `Pure` part of
core's `LawfulMonadLift`, for a source that only has `Pure`, such as a shape of choices. Instances
are declared for this class. -/
class LawfulPureLift (n : semiOutParam (Type u → Type*)) (o : Type u → Type*) [Pure n] [Pure o]
    [inst : MonadLift n o] : Prop where
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (Pure.pure a : n α) = (pure a : o α)

/-- The transitive lift `MonadLiftT m n` sends `Pure.pure a` to `pure a`. Definitions and lemmas
request this class; its instances follow the chain of lifts. -/
class LawfulPureLiftT (m : Type u → Type*) (n : Type u → Type*) [Pure m] [Pure n]
    [inst : MonadLiftT m n] : Prop where
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (Pure.pure a : m α) = (pure a : n α)

instance [Pure m] [Pure n] [Pure o] [MonadLift n o] [MonadLiftT m n] [LawfulPureLift n o]
    [LawfulPureLiftT m n] : LawfulPureLiftT m o where
  monadLift_pure a := (congrArg MonadLift.monadLift (LawfulPureLiftT.monadLift_pure a)).trans
    (LawfulPureLift.monadLift_pure a)

instance [Pure m] : LawfulPureLiftT m m where
  monadLift_pure _ := rfl

instance [Monad n] [Monad o] [MonadLift n o] [LawfulMonadLift n o] : LawfulPureLift n o where
  monadLift_pure := LawfulMonadLift.monadLift_pure

end Complexity
