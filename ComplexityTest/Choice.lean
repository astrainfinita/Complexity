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

-- Guards what `attach` is on the two interpretations, by definition: mathlib's `Multiset.attach`,
-- and the result of a deterministic computation with the proof that it is the result.
example (s : Multiset ℕ) : MonadReturns.attach s = s.attach := rfl

example (x : Id ℕ) : MonadReturns.attach x = pure ⟨x.run, rfl⟩ := rfl

-- Guards what `attach` is for: a fact about every value a computation can return moves into the
-- type of the values, for every predicate and every interpretation. `bind_congr` alone does not
-- give this when the computation returns nothing and no value satisfies the predicate.
example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadReturns m] {P : ℕ → Prop} {x : m ℕ}
    (h : ∀ a ∈ returns x, P a) : ∃ u : m {a // P a}, Subtype.val <$> u = x :=
  ⟨(fun a ↦ ⟨a.1, h a.1 a.2⟩) <$> MonadReturns.attach x, by
    rw [Functor.map_map]; exact MonadReturns.val_map_attach x⟩

-- Guards that the congruence of `bind` on the returned values, a law of the class before `attach`
-- was added, is still available under the same name.
example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadReturns m] {x : m ℕ} {f g : ℕ → m ℕ}
    (h : ∀ a ∈ returns x, f a = g a) : x >>= f = x >>= g :=
  MonadReturns.bind_congr h

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

-- Records how a branch without a successor is treated; a `Multiset` of choices may be empty. The
-- first step either halts in state `9` or goes on for one more step and then has no successor.
-- While it runs, that branch keeps the halting deadline from holding; afterwards it contributes no
-- result and the results no longer change. A change here means such branches count differently.
private def acceptOrStuck : Controller Multiset Unit Unit ℕ where
  q₀ := 0
  halt q := q == 9
  transition q _ := if q = 0 then {(9, ()), (1, ())} else if q = 1 then {(2, ())} else 0

example : ¬∀ c ∈ acceptOrStuck.runFromWith Multiset 0 2, acceptOrStuck.Halted c := by decide

private theorem acceptOrStuck_halted :
    ∀ c ∈ acceptOrStuck.runFromWith Multiset 0 3, acceptOrStuck.Halted c := by decide

example (n : ℕ) (hn : 3 ≤ n) : acceptOrStuck.runFromWith Multiset 0 n = {9} := by
  rw [acceptOrStuck.runFromWith_eq_of_forall_halted Multiset 0 acceptOrStuck_halted hn]
  decide

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
