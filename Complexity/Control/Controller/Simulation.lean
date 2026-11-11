/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Basic
public import Complexity.Control.Transition.Simulation
public import Complexity.Control.LawfulFunctorLift

/-!
# Synchronous simulation of controller runs

One source step corresponds to one target step. `liftRel_runFromWith` holds for every
interpretation of the choices: on `Id` it relates the two runs, and on `Multiset` it matches the
branches one to one, retaining their multiplicities.

For deterministic runs, the step condition is needed only before the segment's endpoint. In
particular, a halted subroutine can be simulated by a machine which continues afterwards.
-/

@[expose] public section

universe u v u' v'

namespace Complexity.Controller

variable {Observation Observation' : Type*} {Action : Type u} {Q : Type v}
  {Config : Type (max u v)}
  [HasState Config Q] [Observe Config Observation] [Apply Config (Q × Action)]

section Deterministic

variable {Action' : Type u'} {Q' : Type v'} {Config' : Type (max u' v')}
  [HasState Config' Q'] [Observe Config' Observation'] [Apply Config' (Q' × Action')]
  (M : Controller Id Observation Action Q) (N : Controller Id Observation' Action' Q')
  {R : Config → Config' → Prop} {c : Config} {d : Config'} {n : ℕ}

/-- Simulate an execution segment whose source has not halted before its endpoint. -/
theorem rel_runFrom_of_not_halted (hcd : R c d)
    (h : ∀ c d, R c d → ¬M.Halted c → R (M.step c) (N.step d))
    (hn : ∀ i < n, ¬M.Halted (M.runFrom c i)) :
    R (M.runFrom c n) (N.runFrom d n) := by
  induction n generalizing c d with
  | zero => exact hcd
  | succ n ih =>
    rw [M.runFrom_succ, N.runFrom_succ]
    exact ih (h c d hcd (hn 0 n.succ_pos)) fun i hi ↦ hn (i + 1) (Nat.succ_lt_succ hi)

/-- A relation preserved by each step is preserved by every finite run. -/
theorem rel_runFrom (h : ∀ c d, R c d → R (M.step c) (N.step d)) (hcd : R c d) (n : ℕ) :
    R (M.runFrom c n) (N.runFrom d n) := by
  induction n generalizing c d with
  | zero => exact hcd
  | succ n ih => exact ih (h c d hcd)

end Deterministic

section Interpreted

variable {Action' : Type u} {Q' : Type v} {Config' : Type (max u v)}
  [HasState Config' Q'] [Observe Config' Observation'] [Apply Config' (Q' × Action')]
  {F F' : Type (max u v) → Type*} (m : Type (max u v) → Type*) [Monad m] [LawfulMonad m]
  [MonadLiftT F m] [MonadLiftT F' m]
  (M : Controller F Observation Action Q) (N : Controller F' Observation' Action' Q')
  {R : Config → Config' → Prop} {c : Config} {d : Config'}

/-- A step of a machine whose transition is the image under `φ` of the source's lifts the
relation: the two machines halt together, and every chosen action keeps the relation. Both steps
are then images of the same choice. -/
theorem liftRel_stepWith_of_map [Functor F] [LawfulFunctorLiftT F m]
    {M : Controller F Observation Action Q} {N : Controller F Observation' Action' Q'}
    (hcd : R c d) (hh : N.Halted d ↔ M.Halted c) (φ : Q × Action → Q' × Action')
    (ht : N.transition (state d) (observe d) = φ <$> M.transition (state c) (observe c))
    (ha : ∀ a, R (apply a c) (apply (φ a) d)) : LiftRel R (M.stepWith m c) (N.stepWith m d) := by
  by_cases hc : M.Halted c
  · rw [M.stepWith_of_halted m c hc, N.stepWith_of_halted m d (hh.mpr hc)]
    exact .pure hcd
  · rw [M.stepWith_of_not_halted m c hc, N.stepWith_of_not_halted m d (mt hh.mp hc), ht,
      LawfulFunctorLiftT.monadLift_map, Functor.map_map]
    exact .map_map _ ha

/-- A relation that every step lifts is lifted by every finite run, for every interpretation `m`
of the choices. Since one monad interprets both machines, both configurations live in one
universe. -/
theorem liftRel_runFromWith
    (h : ∀ c d, R c d → LiftRel R (M.stepWith m c) (N.stepWith m d)) (hcd : R c d) (n : ℕ) :
    LiftRel R (M.runFromWith m c n) (N.runFromWith m d n) :=
  Transition.liftRel_runN h hcd n

end Interpreted

end Complexity.Controller
