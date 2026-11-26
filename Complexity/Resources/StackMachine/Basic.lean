/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.RawWord
public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Control.BinaryChoice.Basic
import Complexity.Models.StackMachine.Reindex
import Mathlib.Data.Fintype.EquivFin

/-!
# Time and space complexity on stack machines

Finite machines act on bit strings. Time counts transitions; space is the largest total
number of symbols on the work stacks, excluding the read-only input and append-only output.

The model is stated once for every choice shape and interpretation, `TimeSpaceModel.stackWith`;
`TimeSpaceModel.stack` is its deterministic instance and `TimeSpaceModel.nstack` its instance with
binary choices on `Multiset`. `TimeSpaceModel.mem_behaviors_stackWith_iff_exists_fin` normalizes
any behavior to a machine indexed by `Fin k` work stacks and `Fin q` control states.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- Finite stack machines on bit strings, with choices of shape `F` interpreted in `m`,
transition time and peak work-stack space. Each behavior is realized by one machine for all
inputs: on every history both measurements stay within budget, and at some step every result has
halted with the corresponding output. -/
def _root_.Complexity.TimeSpaceModel.stackWith (F : Type → Type*) (m : Type → Type*) [Monad m]
    [MonadLiftT F m] [MonadReturns m] : TimeSpaceModel m (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : StackMachine F κ Bool Q), R = fun (xs : RawWord Bool) ys =>
        M.ComputesWithinWith m xs.toList (RawWord.toList <$> ys)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Finite stack machines with transition time and peak work-stack space. This is the
deterministic instance of `TimeSpaceModel.stackWith`. -/
@[simps! inputSize]
def _root_.Complexity.TimeSpaceModel.stack : TimeSpaceModel Id (RawWord Bool) :=
  TimeSpaceModel.stackWith Id Id

/-- Finite binary-choice stack machines, retaining all branch outputs and their multiplicities.
Resource bounds cover every branch, including rejecting branches. The outputs are read at any step
by which every branch has halted. This is the instance of `TimeSpaceModel.stackWith` with binary
choices interpreted in `Multiset`. -/
def _root_.Complexity.TimeSpaceModel.nstack : TimeSpaceModel Multiset (RawWord Bool) :=
  TimeSpaceModel.stackWith BinaryChoice Multiset

/-- Every behavior of `TimeSpaceModel.stackWith F m` is realized by a machine whose work stacks
and control states are indexed by `Fin k` and `Fin q`. -/
theorem _root_.Complexity.TimeSpaceModel.mem_behaviors_stackWith_iff_exists_fin
    {F m : Type → Type*} [Functor F] [Monad m]
    [LawfulMonad m] [MonadLiftT F m] [LawfulFunctorLiftT F m] [MonadReturns m]
    {R : RawWord Bool → m (RawWord Bool) → ℕ → ℕ → Prop} :
    R ∈ (TimeSpaceModel.stackWith F m).behaviors ↔
      ∃ (k q : ℕ) (M : StackMachine F (Fin k) Bool (Fin q)),
        R = fun xs ys ↦ M.ComputesWithinWith m xs.toList (RawWord.toList <$> ys) := by
  constructor
  · rintro ⟨κ, hκ, Q, hQ, M, rfl⟩
    have := Fintype.ofFinite Q
    refine ⟨Fintype.card κ, Fintype.card Q, M.reindex (Fintype.equivFin κ) (Fintype.equivFin Q), ?_⟩
    funext xs ys t s
    simp only [computesWithinWith_reindex_iff]
  · rintro ⟨k, q, M, rfl⟩
    exact ⟨Fin k, inferInstance, Fin q, inferInstance, M, rfl⟩

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- One stack machine with budgets depending on its input value. -/
def Computes {κ Q : Type} [Fintype κ] (M : StackMachine Id κ Bool Q)
    (f : α → β) (t s : α → ℕ) : Prop :=
  Encoding.Computes f fun value (input output : RawWord Bool) =>
    M.ComputesWithin input.toList output.toList (t value) (s value)

theorem computableWithin_iff {f : α → β} {t s : α → ℕ} :
    TimeSpaceModel.stack.ComputableWithin f t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : StackMachine Id κ Bool Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    exact ⟨κ, hκ, Q, hQ, M, h⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    exact ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩

theorem Computes.mono {κ Q : Type} [Fintype κ] {M : StackMachine Id κ Bool Q}
    {f : α → β} {t s t' s' : α → ℕ} (h : Computes M f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) : Computes M f t' s' :=
  Encoding.Computes.mono h (fun hc => hc.mono (ht _) (hs _))

theorem Computes.computableWithin {κ Q : Type} [Fintype κ] [Finite Q]
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : α → ℕ}
    (h : Computes M f t s) : TimeSpaceModel.stack.ComputableWithin f t s :=
  computableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.StackMachine
