/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.ModelTheory.Term
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Order.Hom.BoundedLattice

/-!
# First-order language of Boolean algebras

This file defines the language of Boolean algebras and the operations on its terms.

## Main definitions

- `FirstOrder.Language.booleanAlgebra`: the language with function symbols `⊓`, `⊔`, `ᶜ`, `⊥`, `⊤`.
- `FirstOrder.BooleanAlgebra.CompatibleBooleanAlgebra`: compatibility between a language structure
  and the existing `Min`, `Max`, `Compl`, `Bot`, and `Top` operations.
- `FirstOrder.BooleanAlgebra.compatibleBooleanAlgebraOfBooleanAlgebra`: interpret the language
  using existing Boolean operations.
- `FirstOrder.BooleanAlgebra.languageEquivEquivOrderIso`: language isomorphisms between Boolean
  algebras correspond to order isomorphisms.

Compatibility relates the five operations without asserting the Boolean algebra axioms.
-/

@[expose] public section

variable {α : Type*}

namespace FirstOrder

/-- The function symbols of Boolean algebras, indexed by their arities. -/
inductive booleanAlgebraFunc : ℕ → Type
  | inf : booleanAlgebraFunc 2
  | sup : booleanAlgebraFunc 2
  | compl : booleanAlgebraFunc 1
  | bot : booleanAlgebraFunc 0
  | top : booleanAlgebraFunc 0
  deriving DecidableEq

/-- The language of Boolean algebras has the operations `⊓`, `⊔`, `ᶜ`, `⊥`, `⊤` and no relations. -/
def Language.booleanAlgebra : Language :=
  { Functions := booleanAlgebraFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace BooleanAlgebra

open booleanAlgebraFunc Language

/-- The binary infimum symbol in the language of Boolean algebras. -/
abbrev infFunc : Language.booleanAlgebra.Functions 2 := .inf

/-- The binary supremum symbol in the language of Boolean algebras. -/
abbrev supFunc : Language.booleanAlgebra.Functions 2 := .sup

/-- The unary complement symbol in the language of Boolean algebras. -/
abbrev complFunc : Language.booleanAlgebra.Functions 1 := .compl

/-- The bottom constant in the language of Boolean algebras. -/
abbrev botFunc : Language.booleanAlgebra.Functions 0 := .bot

/-- The top constant in the language of Boolean algebras. -/
abbrev topFunc : Language.booleanAlgebra.Functions 0 := .top

instance (α : Type*) : Min (Language.booleanAlgebra.Term α) :=
  ⟨infFunc.apply₂⟩

theorem inf_def (α : Type*) (t₁ t₂ : Language.booleanAlgebra.Term α) :
    t₁ ⊓ t₂ = infFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Max (Language.booleanAlgebra.Term α) :=
  ⟨supFunc.apply₂⟩

theorem sup_def (α : Type*) (t₁ t₂ : Language.booleanAlgebra.Term α) :
    t₁ ⊔ t₂ = supFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Compl (Language.booleanAlgebra.Term α) :=
  ⟨complFunc.apply₁⟩

theorem compl_def (α : Type*) (t : Language.booleanAlgebra.Term α) :
    tᶜ = complFunc.apply₁ t := rfl

instance (α : Type*) : Bot (Language.booleanAlgebra.Term α) :=
  ⟨Constants.term botFunc⟩

theorem bot_def (α : Type*) : (⊥ : Language.booleanAlgebra.Term α) =
    Constants.term botFunc := rfl

instance (α : Type*) : Top (Language.booleanAlgebra.Term α) :=
  ⟨Constants.term topFunc⟩

theorem top_def (α : Type*) : (⊤ : Language.booleanAlgebra.Term α) =
    Constants.term topFunc := rfl

set_option backward.isDefEq.respectTransparency false in
instance : Fintype Language.booleanAlgebra.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .inf⟩,
       Sum.inl ⟨2, .sup⟩,
       Sum.inl ⟨1, .compl⟩,
       Sum.inl ⟨0, .bot⟩,
       Sum.inl ⟨0, .top⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f ⟩

@[simp]
theorem card_booleanAlgebra : card Language.booleanAlgebra = 5 := by
  have : Fintype.card Language.booleanAlgebra.Symbols = 5 := rfl
  simp [Language.card, this]

open Structure

/-- A language structure compatible with the existing Boolean operations on `B`, without
asserting the Boolean algebra axioms. -/
class CompatibleBooleanAlgebra (B : Type*) [Min B] [Max B] [Compl B] [Bot B] [Top B]
    extends Language.booleanAlgebra.Structure B where
  /-- The infimum symbol is interpreted as the existing infimum operation. -/
  funMap_inf : ∀ x, funMap infFunc x = x 0 ⊓ x 1
  /-- The supremum symbol is interpreted as the existing supremum operation. -/
  funMap_sup : ∀ x, funMap supFunc x = x 0 ⊔ x 1
  /-- The complement symbol is interpreted as the existing complement operation. -/
  funMap_compl : ∀ x, funMap complFunc x = (x 0)ᶜ
  /-- The bottom symbol is interpreted as the existing bottom element. -/
  funMap_bot : ∀ x, funMap (botFunc : Language.booleanAlgebra.Constants) x = ⊥
  /-- The top symbol is interpreted as the existing top element. -/
  funMap_top : ∀ x, funMap (topFunc : Language.booleanAlgebra.Constants) x = ⊤

open CompatibleBooleanAlgebra

attribute [simp] funMap_inf funMap_sup funMap_compl funMap_bot funMap_top

section

variable {B : Type*} [Min B] [Max B] [Compl B] [Bot B] [Top B] [CompatibleBooleanAlgebra B]

@[simp]
theorem realize_inf (x y : booleanAlgebra.Term α) (v : α → B) :
    Term.realize v (x ⊓ y) = Term.realize v x ⊓ Term.realize v y := by
  simp [inf_def]

@[simp]
theorem realize_sup (x y : booleanAlgebra.Term α) (v : α → B) :
    Term.realize v (x ⊔ y) = Term.realize v x ⊔ Term.realize v y := by
  simp [sup_def]

@[simp]
theorem realize_compl (x : booleanAlgebra.Term α) (v : α → B) :
    Term.realize v xᶜ = (Term.realize v x)ᶜ := by
  simp [compl_def]

@[simp]
theorem realize_bot (v : α → B) : Term.realize v (⊥ : booleanAlgebra.Term α) = ⊥ := by
  simp [bot_def, constantMap]

@[simp]
theorem realize_top (v : α → B) : Term.realize v (⊤ : booleanAlgebra.Term α) = ⊤ := by
  simp [top_def, constantMap]

end

@[simp] theorem numFuncs_inf (x y : booleanAlgebra.Term α) :
    (x ⊓ y).numFuncs = x.numFuncs + y.numFuncs + 1 := by
  simp [inf_def]

@[simp] theorem numFuncs_sup (x y : booleanAlgebra.Term α) :
    (x ⊔ y).numFuncs = x.numFuncs + y.numFuncs + 1 := by
  simp [sup_def]

@[simp] theorem numFuncs_compl (x : booleanAlgebra.Term α) : xᶜ.numFuncs = x.numFuncs + 1 := by
  simp [compl_def]

@[simp] theorem numFuncs_bot : (⊥ : booleanAlgebra.Term α).numFuncs = 1 := by
  simp [bot_def]

@[simp] theorem numFuncs_top : (⊤ : booleanAlgebra.Term α).numFuncs = 1 := by
  simp [top_def]

/-- Interpret the language of Boolean algebras using the five operations already on `B`. -/
@[instance_reducible]
def compatibleBooleanAlgebraOfBooleanAlgebra (B : Type*)
    [Min B] [Max B] [Compl B] [Bot B] [Top B] : CompatibleBooleanAlgebra B :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .inf => fun x => x 0 ⊓ x 1
      | _, .sup => fun x => x 0 ⊔ x 1
      | _, .compl => fun x => (x 0)ᶜ
      | _, .bot => fun _ => ⊥
      | _, .top => fun _ => ⊤
    funMap_inf := fun _ => rfl
    funMap_sup := fun _ => rfl
    funMap_compl := fun _ => rfl
    funMap_bot := fun _ => rfl
    funMap_top := fun _ => rfl }

/-- Interpret the Boolean algebra language by the standard operations on `Bool`. -/
instance : CompatibleBooleanAlgebra Bool :=
  compatibleBooleanAlgebraOfBooleanAlgebra Bool

/-- Language isomorphisms between Boolean algebras are exactly order isomorphisms. -/
def languageEquivEquivOrderIso {B C : Type*} [BooleanAlgebra B] [BooleanAlgebra C]
    [CompatibleBooleanAlgebra B] [CompatibleBooleanAlgebra C] :
    Language.booleanAlgebra.Equiv B C ≃ (B ≃o C) where
  toFun f :=
    { f.toEquiv with
      map_rel_iff' := by
        intro x y
        have h : f (x ⊓ y) = f x ⊓ f y := by
          simpa using! f.map_fun infFunc ![x, y]
        change f x ≤ f y ↔ x ≤ y
        rw [← inf_eq_left, ← h, f.injective.eq_iff, inf_eq_left] }
  invFun f :=
    { f.toEquiv with
      map_fun' := fun {n} g => by
        cases g <;> simp [map_compl']
      map_rel' := fun {n} r => by cases r }

variable (B : Type*) [Language.booleanAlgebra.Structure B]

/-- Recover an infimum operation from a language structure. -/
abbrev infOfBooleanAlgebraStructure : Min B :=
  ⟨fun x y => funMap infFunc ![x, y]⟩

/-- Recover a supremum operation from a language structure. -/
abbrev supOfBooleanAlgebraStructure : Max B :=
  ⟨fun x y => funMap supFunc ![x, y]⟩

/-- Recover a complement operation from a language structure. -/
abbrev complOfBooleanAlgebraStructure : Compl B :=
  ⟨fun x => funMap complFunc ![x]⟩

/-- Recover a bottom element from a language structure. -/
abbrev botOfBooleanAlgebraStructure : Bot B :=
  ⟨funMap botFunc ![]⟩

/-- Recover a top element from a language structure. -/
abbrev topOfBooleanAlgebraStructure : Top B :=
  ⟨funMap topFunc ![]⟩

attribute [local instance] infOfBooleanAlgebraStructure supOfBooleanAlgebraStructure
  complOfBooleanAlgebraStructure botOfBooleanAlgebraStructure topOfBooleanAlgebraStructure

/-- The operations recovered from a language structure are compatible with that structure. -/
abbrev compatibleBooleanAlgebraOfBooleanAlgebraStructure : CompatibleBooleanAlgebra B :=
  { funMap_inf := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_sup := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_compl := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_bot := by
      simp only [Fin.forall_fin_zero_pi]
      rfl
    funMap_top := by
      simp only [Fin.forall_fin_zero_pi]
      rfl }

end BooleanAlgebra

end FirstOrder
