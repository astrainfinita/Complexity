/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Direct enumerations for finite control values

These instances use arithmetic bijections instead of constructing lists and searching them.
Dependent sums still compute every branch's size; this can traverse many source branches.
Finite functions and vectors number coordinates without listing all possible values.
-/

@[expose] public section

open scoped BigOperators

instance (priority := 1100) PEmpty.instFinEnumDirect : FinEnum PEmpty where
  card := 0
  equiv := Equiv.equivOfIsEmpty _ _

instance (priority := 1100) PUnit.instFinEnumDirect : FinEnum PUnit where
  card := 1
  equiv := Equiv.ofUnique _ _

instance Bool.instFinEnum : FinEnum Bool where
  card := 2
  equiv := finTwoEquiv.symm

instance Option.instFinEnum {α : Type*} [FinEnum α] : FinEnum (Option α) where
  card := FinEnum.card α + 1
  equiv := (Equiv.optionCongr FinEnum.equiv).trans (finSuccEquiv _).symm

instance (priority := 1100) Fin.instFinEnumDirect (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := ⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance (priority := 1100) Prod.instFinEnumDirect {α β : Type*}
    [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  card := FinEnum.card α * FinEnum.card β
  equiv := (Equiv.prodCongr FinEnum.equiv FinEnum.equiv).trans finProdFinEquiv

instance (priority := 1100) Sum.instFinEnumDirect {α β : Type*}
    [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  card := FinEnum.card α + FinEnum.card β
  equiv := (Equiv.sumCongr FinEnum.equiv FinEnum.equiv).trans finSumFinEquiv

/-- Number a dependent pair by the preceding branch sizes and its rank inside its branch. -/
instance (priority := 1100) Sigma.instFinEnumDirect {α : Type*} {β : α → Type*}
    [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) where
  card := ∑ i : Fin (FinEnum.card α), FinEnum.card (β (FinEnum.equiv.symm i))
  equiv := (Equiv.sigmaCongrLeft' (FinEnum.equiv (α := α))).trans
    ((Equiv.sigmaCongrRight (fun i ↦ (FinEnum.equiv (α := β (FinEnum.equiv.symm i))))).trans
      finSigmaFinEquiv)

/-- Number a finite dependent function by the mixed-radix representation of its coordinates. -/
instance (priority := 1100) Pi.instFinEnumDirect {α : Type*} {β : α → Type*}
    [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum ((a : α) → β a) where
  card := ∏ i : Fin (FinEnum.card α), FinEnum.card (β (FinEnum.equiv.symm i))
  equiv := (Equiv.piCongrLeft' β (FinEnum.equiv (α := α))).trans
    ((Equiv.piCongrRight (fun i ↦ (FinEnum.equiv (α := β (FinEnum.equiv.symm i))))).trans
      finPiFinEquiv)

/-- Reuse coordinate numbering for an array-backed vector. -/
instance (priority := 1100) Vector.instFinEnumDirect {α : Type*} [FinEnum α] {n : ℕ} :
    FinEnum (Vector α n) :=
  FinEnum.ofEquiv (Fin n → α)
    { toFun := fun a i ↦ a[i.val]
      invFun := Vector.ofFn
      left_inv := fun _ ↦ Vector.ofFn_getElem
      right_inv := by intro f; funext i; simp only [Vector.getElem_ofFn] }
