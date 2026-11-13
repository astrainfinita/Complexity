/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice.Probability
import Complexity.Control.Controller.Basic
meta import Complexity.Control.Controller.Basic
meta import Complexity.Control.BinaryChoice.Basic

open Complexity

-- Successive choices can take different branch indices; they do not share a Reader input.
#guard ((do
    let i ← monadLift (m := BinaryChoice) (fun i => i)
    let j ← monadLift (m := BinaryChoice) (fun j => j)
    pure (i, j)) : Multiset (Fin 2 × Fin 2)) =
  ↑([(0, 0), (0, 1), (1, 0), (1, 1)] : List (Fin 2 × Fin 2))

-- Coincident endpoints retain the multiplicity of the two paths.
#guard (monadLift (m := BinaryChoice) (fun _ => true) : Multiset Bool) = ↑[true, true]
#guard (monadLift (m := BinaryChoice) (fun _ => true) : Multiset Bool).count true = 2

-- Swapping the two branch labels changes neither the collection nor its multiplicities.
example {α : Type*} (a b : α) :
    (monadLift (m := BinaryChoice) (fun i => if i = 0 then a else b) : Multiset α) =
      (monadLift (m := BinaryChoice) (fun i => if i = 0 then b else a) : Multiset α) := by
  change a ::ₘ b ::ₘ (0 : Multiset α) = b ::ₘ a ::ₘ 0
  exact Multiset.cons_swap a b 0

-- Under the probabilistic interpretation coincident endpoints instead add their masses.
example : (monadLift (m := BinaryChoice) (fun _ => true) : PMF Bool) = PMF.pure true := by
  exact PMF.map_const _ _

-- Each labelled branch has probability one half.
example (i : Fin 2) :
    (monadLift (m := BinaryChoice) (fun j => j) : PMF (Fin 2)) i = (2 : ENNReal)⁻¹ := by
  simp [PMF.uniformOfFintype_apply]

-- Two separately interpreted choices give every ordered pair probability one quarter.
example (i j : Fin 2) :
    ((monadLift (m := BinaryChoice) id : PMF (Fin 2)).bind fun a =>
      (monadLift (m := BinaryChoice) id : PMF (Fin 2)).map fun b => (a, b)) (i, j) =
      (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    Prod.mk.injEq, ite_and, mul_ite]

-- Guards that lawful lifts declared one step at a time extend along chains of lifts, including
-- monad transformers, to the class requested by the simulation lemmas.
example : LawfulFunctorLiftT BinaryChoice Multiset := inferInstance
example : LawfulFunctorLiftT BinaryChoice (StateT ℕ Multiset) := inferInstance
example : LawfulFunctorLiftT Id Id := inferInstance

-- Guards what `returns` is on the two interpretations, by definition: the result on `Id`, the
-- members on `Multiset`. A generic fact about every value a computation can return is then the
-- plain statement about every branch, with no conversion.
example (x : Id ℕ) (a : ℕ) : a ∈ returns x ↔ a = x.run := Iff.rfl

example (s : Multiset ℕ) (P : ℕ → Prop) : (∀ a ∈ returns s, P a) = (∀ a ∈ s, P a) := rfl

-- Multiset interpretations may have more than two alternatives, with coincident endpoints.
private def threeChoices : Controller Multiset Unit Unit ℕ where
  q₀ := 0
  halt q := q != 0
  transition _ _ := ↑[(1, ()), (1, ()), (2, ())]

private instance : Controller.HasState ℕ ℕ where
  state := id

private instance : Controller.Observe ℕ Unit where
  observe _ := ()

private instance : Controller.Apply ℕ (ℕ × Unit) where
  apply a _ := a.1

-- Halting freezes the three paths without collapsing their repeated endpoint.
example (n : ℕ) (hn : 1 ≤ n) :
    threeChoices.runFromWith Multiset 0 n = ↑[1, 1, 2] := by
  apply threeChoices.runFromWith_eq_of_forall_halted Multiset 0 (hn := hn)
  intro d hd
  change d ∈ (↑[1, 1, 2] : Multiset ℕ) at hd
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

-- The same controller can use a local interpretation for the same target monad.
private def binaryChoices : Controller BinaryChoice Unit Unit ℕ where
  q₀ := 0
  halt q := q != 0
  transition _ _ i := if i = 0 then (1, ()) else (2, ())

#guard binaryChoices.runFromWith Multiset 0 1 = ↑[1, 2]

section

local instance : MonadLift BinaryChoice Multiset where
  monadLift f := {f 0}

#guard binaryChoices.runFromWith Multiset 0 1 = {1}

end

-- The local choice does not replace the default interpretation outside its scope.
#guard binaryChoices.runFromWith Multiset 0 1 = ↑[1, 2]
