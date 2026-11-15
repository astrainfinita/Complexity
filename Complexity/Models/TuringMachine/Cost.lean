/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Basic
public import Complexity.Models.TuringMachine.History
public import Complexity.Control.Controller.Cost

/-!
# Time and visited-cell space of Turing-machine histories

`ComputesWithinWith` is the specification of this model for every choice shape and every
interpretation: `Controller.ComputesWithinCostWith` with the number of transitions as time and the
visited work cells as space. The deterministic `ComputesWithin` is its instance on `Id`. The
parameters `κ`, `Γ` and `Q` of the specification share one universe, because
`Controller.ComputesWithinCostWith` keeps outputs in the universe of the results; this is a current
limitation, not a decision.
-/

@[expose] public section

namespace Complexity.TM

open Controller (History)

variable {κ Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Extending a run can only enlarge its visited intervals. -/
theorem runHistoryFrom_visited_mono (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).snd.visited :=
  fun _ _ h ↦ M.configSup_runHistoryFrom_mono _ c h

theorem runHistoryFrom_space_mono [Fintype κ] (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).snd.space :=
  fun _ _ h ↦ History.space_mono (M.runHistoryFrom_visited_mono c h)

/-- An interval bounds a tape's visits exactly when it contains every bounded-run head. -/
theorem runHistoryFrom_visited_le_iff (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs)
    (n : ℕ) (i : κ) (v : NonemptyInterval ℤ) :
    (M.runHistoryFrom c n).snd.visited i ≤ v ↔
      ∀ m ≤ n, (M.runFrom c m).2.workPos i ∈ v := by
  simp only [History.visited_apply_le_iff, History.configs_snd, List.mem_map,
    Controller.mem_configs_runHistoryFrom, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

section ComputesWithinWith

universe u

/-- Compute in the interpretation `m` with unit action time and visited-cell space: every history
of the run stays within both budgets, and at some step every result has halted with the
corresponding output. -/
def ComputesWithinWith {F : Type u → Type*} {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ]
    (m : Type u → Type*) [Monad m] [MonadLiftT F m] [MonadReturns m] (M : TM F κ Γ Q)
    (xs : List Γ) (outs : m (List Γ)) (t s : ℕ) : Prop :=
  M.ComputesWithinCostWith m xs outs History.length History.space t s

/-- Enlarging budgets keeps the same outputs. -/
theorem ComputesWithinWith.mono {F : Type u → Type*} {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ]
    {m : Type u → Type*} [Monad m] [MonadLiftT F m] [MonadReturns m] {M : TM F κ Γ Q}
    {xs : List Γ} {outs : m (List Γ)} {t s t' s' : ℕ} (h : M.ComputesWithinWith m xs outs t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesWithinWith m xs outs t' s' :=
  Controller.computesWithinCostWith_mono h ht hs

end ComputesWithinWith

end Complexity.TM
