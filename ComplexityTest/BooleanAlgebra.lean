/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Set

open FirstOrder FirstOrder.Language FirstOrder.BooleanAlgebra

namespace Complexity.BooleanAlgebraTest

variable {α : Type*}

set_option backward.isDefEq.respectTransparency false in
example (n : ℕ) : DecidableEq (booleanAlgebra.Functions n) := inferInstance

example (n : ℕ) : DecidableEq (booleanAlgebra.Relations n) := inferInstance

example : IsAlgebraic booleanAlgebra := inferInstance

example : Fintype.card booleanAlgebra.Symbols = 5 := rfl

section Bool

local instance : CompatibleBooleanAlgebra Bool := compatibleBooleanAlgebraOfBooleanAlgebra Bool

-- A compound term uses all five symbols and evaluates using the ordinary Boolean operations.
example (v : Fin 2 → Bool) :
    Term.realize v
      ((((Term.var 0 ⊓ Term.var 1)ᶜ ⊔ ⊥) ⊓ ⊤) : booleanAlgebra.Term (Fin 2)) =
      !(v 0 && v 1) := by
  simp

-- Quantified formulas interpret the algebraic operations, not formula-level connectives.
example : Bool ⊨ (∀' ((&0 ⊓ (&0)ᶜ) =' ⊥) : booleanAlgebra.Sentence) := by
  simp [Sentence.Realize, Formula.Realize]

end Bool

section Sets

local instance : CompatibleBooleanAlgebra (Set α) :=
  compatibleBooleanAlgebraOfBooleanAlgebra (Set α)

-- The same language works on powerset algebras, with an arbitrary variable type.
example {ι : Type*} (v : ι → Set α) (s t : booleanAlgebra.Term ι) :
    Term.realize v ((s ⊔ t)ᶜ ⊓ ⊤) = (Term.realize v s ∪ Term.realize v t)ᶜ := by
  simp

-- Boolean algebra laws become true first-order sentences under the interpretation.
example : Set α ⊨ (∀' (((&0)ᶜ ⊔ &0) =' ⊤) : booleanAlgebra.Sentence) := by
  simp [Sentence.Realize, Formula.Realize]

end Sets

section Isomorphisms

variable {B C : Type*} [BooleanAlgebra B] [BooleanAlgebra C]
  [CompatibleBooleanAlgebra B] [CompatibleBooleanAlgebra C]

-- Both conversions retain the underlying map, including across different carriers.
example (f : booleanAlgebra.Equiv B C) (x : B) :
    languageEquivEquivOrderIso f x = f x := rfl

example (f : B ≃o C) (x : B) :
    languageEquivEquivOrderIso.symm f x = f x := rfl

example (f : booleanAlgebra.Equiv B C) :
    languageEquivEquivOrderIso.symm (languageEquivEquivOrderIso f) = f :=
  languageEquivEquivOrderIso.symm_apply_apply f

example (f : B ≃o C) :
    languageEquivEquivOrderIso (languageEquivEquivOrderIso.symm f) = f :=
  languageEquivEquivOrderIso.apply_symm_apply f

-- An order isomorphism transported to the language preserves nested terms.
example (f : B ≃o C) (v : α → B) (t : booleanAlgebra.Term α) :
    f (Term.realize v t) = Term.realize (f ∘ v) t := by
  exact (HomClass.realize_term (languageEquivEquivOrderIso.symm f)).symm

end Isomorphisms

section RecoveredOperations

variable (B : Type*) [S : booleanAlgebra.Structure B]

local instance : Min B := infOfBooleanAlgebraStructure B
local instance : Max B := supOfBooleanAlgebraStructure B
local instance : Compl B := complOfBooleanAlgebraStructure B
local instance : Bot B := botOfBooleanAlgebraStructure B
local instance : Top B := topOfBooleanAlgebraStructure B
local instance : CompatibleBooleanAlgebra B :=
  compatibleBooleanAlgebraOfBooleanAlgebraStructure B

-- Extracting operations and their compatibility preserves the original language structure.
example : (compatibleBooleanAlgebraOfBooleanAlgebraStructure B).toStructure = S := rfl

-- The semantic API also works for arbitrary structures, without assuming Boolean algebra laws.
example (v : α → B) (s t : booleanAlgebra.Term α) :
    Term.realize v ((s ⊓ tᶜ) ⊔ ⊥) =
      (Term.realize v s ⊓ (Term.realize v t)ᶜ) ⊔ (⊥ : B) := by
  simp

end RecoveredOperations

end Complexity.BooleanAlgebraTest
