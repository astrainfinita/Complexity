/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.LawfulFunctorLift
meta import Lean.Meta.CoeAttr

/-!
# Quantifiers over the results of a computation

A quantifier `Q : MonadQuant m` says what it means that a computation `x : m α` satisfies a
predicate on its results: `Q P x`. It is monotone and turns `pure` and `>>=` into the
corresponding operations on predicates, so that `Q P (pure a) ↔ P a` and
`Q P (x >>= f) ↔ Q (fun a ↦ Q P (f a)) x`. A quantifier is a value bundling the function with its
laws rather than an instance: one monad has several, such as every and some value a multiset can
return (`MonadQuant.all`, `MonadQuant.any`), or the two readings of an alternating game.

`MonadQuant.PureLift` and `MonadQuant.PureLiftT` say that a lift reads `Pure.pure a` of a choice
shape as `a`, as `LawfulFunctorLift` and `LawfulFunctorLiftT` do for mapping results: instances
are declared for the one-step class, and definitions and lemmas request the transitive one. A lift
sending `Pure.pure` to `pure` (`LawfulPureLift`) is read correctly by every quantifier.

The binder of the result type is strict-implicit, `⦃α⦄`, so that the function of a quantifier is
instantiated at a result type only when it is applied to a predicate.
-/

@[expose] public section

universe u v w

namespace Complexity

/-- A quantifier over the results of computations in `m`: monotone in the predicate, and a
morphism of monads into predicates, with `pure` and `bind` read as equivalences. -/
structure MonadQuant (m : Type u → Type v) [Monad m] where
  /-- `Q P x`: the computation `x` satisfies the predicate `P` on its results. -/
  toFun : ⦃α : Type u⦄ → (α → Prop) → m α → Prop
  /-- A weaker predicate holds of the same computation. -/
  mono {α : Type u} {P P' : α → Prop} {x : m α} : (∀ a, P a → P' a) → toFun P x → toFun P' x
  /-- `pure a` satisfies a predicate exactly when `a` does. -/
  pure_iff {α : Type u} {P : α → Prop} {a : α} : toFun P (pure a) ↔ P a
  /-- `x >>= f` satisfies a predicate exactly when `x` satisfies it after each continuation. -/
  bind_iff {α β : Type u} {P : β → Prop} {x : m α} {f : α → m β} :
    toFun P (x >>= f) ↔ toFun (fun a ↦ toFun P (f a)) x

namespace MonadQuant

variable {m : Type u → Type v} [Monad m] {α β : Type u}

instance : CoeFun (MonadQuant m) fun _ ↦ ⦃α : Type u⦄ → (α → Prop) → m α → Prop :=
  ⟨MonadQuant.toFun⟩

/- Register `MonadQuant.toFun` as a function coercion, so that goals show `Q P x`, as mathlib
does for `DFunLike.coe`. -/
open Lean Elab Command in
run_cmd liftTermElabM do
  Lean.Meta.registerCoercion ``MonadQuant.toFun
    (some { numArgs := 3, coercee := 2, type := .coeFun })

/-- The one-step lift `MonadLift n m` sends `Pure.pure a` to a computation the quantifier reads as
`a`. Instances are declared for this class; its source need only have `Pure`, such as a shape of
choices. -/
class PureLift (n : semiOutParam (Type u → Type w)) (m : Type u → Type v) [Pure n] [Monad m]
    [inst : MonadLift n m] (Q : MonadQuant m) : Prop where
  /-- The lift of `Pure.pure a` satisfies a predicate exactly when `a` does. -/
  monadLift_pure_iff {α : Type u} {P : α → Prop} {a : α} :
    Q P (inst.monadLift (Pure.pure a : n α)) ↔ P a

/-- The transitive lift `MonadLiftT n m` sends `Pure.pure a` to a computation the quantifier reads
as `a`. Definitions and lemmas request this class. Current state: its instances are the reflexive
lift, and a chain of lifts sending `Pure.pure` to `pure` followed by one `MonadQuant.PureLift`
step; a later step would have to keep the quantifier of every computation, which these classes do
not state. -/
class PureLiftT (n : Type u → Type w) (m : Type u → Type v) [Pure n] [Monad m]
    [inst : MonadLiftT n m] (Q : MonadQuant m) : Prop where
  /-- The lift of `Pure.pure a` satisfies a predicate exactly when `a` does. -/
  monadLift_pure_iff {α : Type u} {P : α → Prop} {a : α} :
    Q P (inst.monadLift (Pure.pure a : n α)) ↔ P a

/-- `f <$> x` satisfies a predicate exactly when `x` satisfies it after `f`. -/
theorem map_iff [LawfulMonad m] (Q : MonadQuant m) {f : α → β} {x : m α} {P : β → Prop} :
    Q P (f <$> x) ↔ Q (fun a ↦ P (f a)) x := by
  simp only [← bind_pure_comp, Q.bind_iff, Q.pure_iff]

/-- The lift of `Pure.pure a` satisfies a predicate exactly when `a` does. -/
theorem monadLift_pure_iff {n : Type u → Type w} [Pure n] [MonadLiftT n m] (Q : MonadQuant m)
    [PureLiftT n m Q] {P : α → Prop} {a : α} : Q P (monadLift (Pure.pure a : n α)) ↔ P a :=
  PureLiftT.monadLift_pure_iff

variable {Q : MonadQuant m}

instance : PureLiftT m m Q where
  monadLift_pure_iff := Q.pure_iff

/-- A chain of lifts sending `Pure.pure` to `pure`, followed by one step read correctly. -/
instance {l : Type u → Type w} {n : Type u → Type*} [Pure l] [Pure n] [MonadLift n m]
    [MonadLiftT l n] [LawfulPureLiftT l n] [PureLift n m Q] : PureLiftT l m Q where
  monadLift_pure_iff {α P a} :=
    (congrArg (fun y : n α ↦ Q P (MonadLift.monadLift y : m α))
      (LawfulPureLiftT.monadLift_pure (m := l) a)).to_iff.trans PureLift.monadLift_pure_iff

/-- A lift sending `Pure.pure a` to `pure a` is read as `a` by every quantifier. -/
instance {n : Type u → Type w} [Pure n] [MonadLift n m] [LawfulPureLift n m] : PureLift n m Q where
  monadLift_pure_iff {_ P a} :=
    (congrArg (Q P) (LawfulPureLift.monadLift_pure (n := n) (o := m) a)).to_iff.trans Q.pure_iff

end MonadQuant

end Complexity
