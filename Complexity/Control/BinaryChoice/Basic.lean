/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Multiset.Functor
public import Complexity.Control.LawfulFunctorLift

/-!
# Binary choices and their multiset interpretation
-/

@[expose] public section

universe u

namespace Complexity

/-- Two labelled alternatives for one machine step; their results may coincide. -/
abbrev BinaryChoice (α : Type*) := Fin 2 → α

namespace BinaryChoice

/-- Apply a function to both alternatives, keeping their labels. -/
instance : Functor BinaryChoice where
  map f x := f ∘ x

@[simp] theorem map_apply {α β : Type u} (f : α → β) (x : BinaryChoice α) (i : Fin 2) :
    (f <$> x) i = f (x i) := rfl

/-- Duplicate one value across both branch labels, as `Controller.toBinary` does. -/
instance : Pure BinaryChoice where
  pure a _ := a

@[simp] theorem pure_apply {α : Type u} (a : α) (i : Fin 2) :
    (pure a : BinaryChoice α) i = a := rfl

/-- Enumerate both alternatives without ordering them, retaining their multiplicities. -/
instance : MonadLift BinaryChoice Multiset where
  monadLift f := ↑[f 0, f 1]

@[simp] theorem monadLift_multiset {α : Type*} (f : BinaryChoice α) :
    (monadLift f : Multiset α) = ↑[f 0, f 1] := rfl

instance : LawfulFunctorLift BinaryChoice Multiset := ⟨fun _ _ ↦ rfl⟩

end BinaryChoice
end Complexity
