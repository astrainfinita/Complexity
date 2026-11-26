/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Deterministic
import Complexity.Control.Controller.Simulation

/-!
# Reindexing work stacks and control states of a stack machine

`StackMachine.reindex eκ eQ` relabels the work stacks along `eκ : κ ≃ κ'` and the control states
along `eQ : Q ≃ Q'`. Every history of the source machine relates via `LiftRel` to its reindexed
history with the same length, peak work-stack mass, halting status, and output
(`liftRel_runHistoryWith_reindex`): on `Id` this relates the two runs, and on `Multiset` it
matches branches one to one with their multiplicities.

Reindexing therefore preserves `ComputesWithinWith` in both directions for every choice shape and
interpretation (`computesWithinWith_reindex_iff`). The converse is proved directly via
`LiftRel.swap` rather than reindexing back by `eκ.symm` and `eQ.symm`, so no `LawfulFunctor F`
instance is needed (in particular, it applies directly to `BinaryChoice`).
-/

@[expose] public section

universe uκ u v

namespace Complexity.StackMachine

section Basic

variable {κ κ' κ'' Γ : Type*}

/-- Relabel the work stacks of an action along `eκ`. -/
@[simps]
def Action.reindex (eκ : κ ≃ κ') (a : Action κ Γ) : Action κ' Γ where
  inputMove := a.inputMove
  work i := a.work (eκ.symm i)
  output := a.output

@[simp] theorem Action.reindex_refl (a : Action κ Γ) : a.reindex (Equiv.refl κ) = a := rfl

@[simp] theorem Action.reindex_reindex (eκ : κ ≃ κ') (eκ' : κ' ≃ κ'') (a : Action κ Γ) :
    (a.reindex eκ).reindex eκ' = a.reindex (eκ.trans eκ') := rfl

@[simp] theorem Action.reindex_idle (eκ : κ ≃ κ') :
    (Action.idle : Action κ Γ).reindex eκ = .idle := rfl

/-- Relabel the work stacks of a configuration along `eκ`. -/
@[simps]
def Cfg.reindex {xs : Array Γ} (eκ : κ ≃ κ') (c : Cfg κ Γ xs) : Cfg κ' Γ xs where
  inputPos := c.inputPos
  «stacks» i := c.stacks (eκ.symm i)
  output := c.output

@[simp] theorem Cfg.reindex_refl {xs : Array Γ} (c : Cfg κ Γ xs) :
    c.reindex (Equiv.refl κ) = c := rfl

@[simp] theorem Cfg.reindex_reindex {xs : Array Γ} (eκ : κ ≃ κ') (eκ' : κ' ≃ κ'')
    (c : Cfg κ Γ xs) : (c.reindex eκ).reindex eκ' = c.reindex (eκ.trans eκ') := rfl

@[simp] theorem Cfg.reindex_init (eκ : κ ≃ κ') (xs : List Γ) :
    (Cfg.init κ xs).reindex eκ = Cfg.init κ' xs := rfl

theorem observe_reindex {xs : Array Γ} (eκ : κ ≃ κ') (c : Cfg κ Γ xs) :
    (observe (c.reindex eκ) : Option Γ × (κ' → Option Γ)) =
      ((observe c : Option Γ × (κ → Option Γ)).1,
        (observe c : Option Γ × (κ → Option Γ)).2 ∘ eκ.symm) := rfl

@[simp] theorem apply_reindex {xs : Array Γ} (eκ : κ ≃ κ') (a : Action κ Γ)
    (c : Cfg κ Γ xs) : apply (a.reindex eκ) (c.reindex eκ) = (apply a c).reindex eκ := rfl

@[simp] theorem Cfg.mass_reindex [Fintype κ] [Fintype κ'] {xs : Array Γ} (eκ : κ ≃ κ')
    (c : Cfg κ Γ xs) : (c.reindex eκ).mass = c.mass :=
  Equiv.sum_comp eκ.symm fun i ↦ (c.stacks i).length

end Basic

/-- Relabel the work stacks along `eκ` and the control states along `eQ`. Every choice is mapped
separately, so the choice shape `F` is unchanged. -/
@[simps]
def reindex {κ κ' : Type uκ} {Γ : Type u} {Q Q' : Type v}
    {F : Type (max uκ u v) → Type*} [Functor F]
    (M : StackMachine F κ Γ Q) (eκ : κ ≃ κ') (eQ : Q ≃ Q') : StackMachine F κ' Γ Q' where
  q₀ := eQ M.q₀
  halt q := M.halt (eQ.symm q)
  transition q v := Prod.map eQ (Action.reindex eκ) <$> M.transition (eQ.symm q) (v.1, v.2 ∘ eκ)

@[simp] theorem reindex_refl {κ : Type uκ} {Γ : Type u} {Q : Type v}
    {F : Type (max uκ u v) → Type*} [Functor F] [LawfulFunctor F]
    (M : StackMachine F κ Γ Q) :
    M.reindex (Equiv.refl κ) (Equiv.refl Q) = M := by
  cases M
  dsimp only [reindex]
  congr 1
  funext q v
  have hmap : Prod.map (Equiv.refl Q) (Action.reindex (Γ := Γ) (Equiv.refl κ)) = id := by
    funext ⟨_, _⟩
    rfl
  rw [hmap, id_map]
  rfl

@[simp] theorem reindex_reindex {κ κ' κ'' : Type uκ} {Γ : Type u} {Q Q' Q'' : Type v}
    {F : Type (max uκ u v) → Type*} [Functor F] [LawfulFunctor F]
    (M : StackMachine F κ Γ Q) (eκ : κ ≃ κ') (eκ' : κ' ≃ κ'') (eQ : Q ≃ Q') (eQ' : Q' ≃ Q'') :
    (M.reindex eκ eQ).reindex eκ' eQ' = M.reindex (eκ.trans eκ') (eQ.trans eQ') := by
  cases M
  simp only [reindex, Equiv.trans_apply, Equiv.symm_trans_apply, Functor.map_map]
  rfl

section History

variable {κ κ' : Type uκ} {Γ : Type u} {Q Q' : Type v}

private theorem last_map_reindex {xs : Array Γ} (eκ : κ ≃ κ') (eQ : Q ≃ Q')
    (p : Controller.History (Q × Cfg κ Γ xs) (Q × Action κ Γ)) :
    (p.map (Prod.map eQ (Cfg.reindex eκ)) (Prod.map eQ (Action.reindex eκ))).last =
      Prod.map eQ (Cfg.reindex eκ) p.last :=
  p.last_map (Prod.map eQ (Cfg.reindex eκ)) (Prod.map eQ (Action.reindex eκ)) fun _ _ ↦ rfl

private theorem configSup_mass_map_reindex [Fintype κ] [Fintype κ'] {xs : Array Γ}
    (eκ : κ ≃ κ') (eQ : Q ≃ Q')
    (p : Controller.History (Q × Cfg κ Γ xs) (Q × Action κ Γ)) :
    (p.map (Prod.map eQ (Cfg.reindex eκ)) (Prod.map eQ (Action.reindex eκ))).snd.configSup
        Cfg.mass =
      p.snd.configSup Cfg.mass := by
  rw [Controller.History.configSup_snd, Controller.History.configSup_snd,
    p.configSup_map (Prod.map eQ (Cfg.reindex eκ)) (Prod.map eQ (Action.reindex eκ))
      (fun _ _ ↦ rfl)]
  simp only [Function.comp_def, Prod.map_snd, Cfg.mass_reindex]

/-- Runs match for every choice shape `F` and every interpretation `m`: each history of `M`
relates via `LiftRel` to its reindexed history of `M.reindex eκ eQ`. On `Id` this relates the two
runs; on `Multiset` every branch corresponds one to one with its multiplicity. -/
theorem liftRel_runHistoryWith_reindex {F : Type (max uκ u v) → Type*} [Functor F]
    (m : Type (max uκ u v) → Type*) [Monad m] [LawfulMonad m] [MonadLiftT F m]
    [LawfulFunctorLiftT F m] (M : StackMachine F κ Γ Q) (eκ : κ ≃ κ') (eQ : Q ≃ Q')
    (xs : List Γ) (n : ℕ) :
    LiftRel (fun p q ↦ q = p.map (Prod.map eQ (Cfg.reindex eκ)) (Prod.map eQ (Action.reindex eκ)))
      (M.runHistoryWith m xs n) ((M.reindex eκ eQ).runHistoryWith m xs n) := by
  rw [Controller.runHistoryWith, Controller.runHistoryWith]
  refine Controller.liftRel_runFromWith m M (M.reindex eκ eQ)
    (R := fun p q ↦ q = Controller.History.map p (Prod.map eQ (Cfg.reindex eκ))
      (Prod.map eQ (Action.reindex eκ)))
    (fun p q hpq ↦ ?_) rfl n
  subst hpq
  have hlast := last_map_reindex eκ eQ p
  refine Controller.liftRel_stepWith_of_map m rfl ?_ (Prod.map eQ (Action.reindex eκ)) ?_
    fun a ↦ (p.map_snoc a _ _).symm
  · simp [Controller.Halted, hlast]
  · simp only [Controller.History.state_def, Controller.History.observe_def, hlast,
      Controller.state_prod, Controller.observe_prod, Prod.map_fst, Prod.map_snd,
      reindex_transition, Equiv.symm_apply_apply, observe_reindex]
    congr 2
    exact Prod.ext rfl (funext fun i ↦ by simp)

end History

section Transfer

variable {κ κ' Γ Q Q' : Type u} {F m : Type u → Type*}
  [Functor F] [Monad m] [LawfulMonad m] [MonadLiftT F m] [LawfulFunctorLiftT F m]

omit [Functor F] [LawfulFunctorLiftT F m] in
private theorem of_liftRel_same_output [MonadReturns m] [Fintype κ] [Fintype κ']
    {M₁ : StackMachine F κ Γ Q} {M₂ : StackMachine F κ' Γ Q'}
    {xs : List Γ} {outs : m (List Γ)} {t s : ℕ}
    {R : Controller.History (Q × Cfg κ Γ xs.toArray) (Q × Action κ Γ) →
      Controller.History (Q' × Cfg κ' Γ xs.toArray) (Q' × Action κ' Γ) → Prop}
    (h : M₁.ComputesWithinWith m xs outs t s)
    (hr : ∀ n, LiftRel R (M₁.runHistoryWith m xs n) (M₂.runHistoryWith m xs n))
    (hb : ∀ p q, R p q →
      p.snd.length ≤ t ∧ p.snd.configSup Cfg.mass ≤ s →
      q.snd.length ≤ t ∧ q.snd.configSup Cfg.mass ≤ s)
    (hh : ∀ p q, R p q → M₁.Halted p → M₂.Halted q)
    (ho : ∀ p q (y : List Γ), R p q → p.last.2.output = y.toArray → q.last.2.output = y.toArray) :
    M₂.ComputesWithinWith m xs outs t s := by
  have h' : M₂.ComputesWithinWith m xs (id <$> outs) t s :=
    Controller.ComputesWithinCostWith.of_liftRel h hr (fun c ↦ c.2.output.toList)
      (fun c y hy ↦ by simp only [hasOutput_isOutput] at hy; rw [hy, List.toList_toArray])
      hb hh ho
  rwa [id_map] at h'

/-- Reindexing preserves `ComputesWithinWith` with the exact same outputs and resource budgets. -/
theorem ComputesWithinWith.reindex [MonadReturns m] [Fintype κ] [Fintype κ']
    {M : StackMachine F κ Γ Q} {xs : List Γ} {outs : m (List Γ)} {t s : ℕ}
    (h : M.ComputesWithinWith m xs outs t s) (eκ : κ ≃ κ') (eQ : Q ≃ Q') :
    (M.reindex eκ eQ).ComputesWithinWith m xs outs t s :=
  of_liftRel_same_output h (liftRel_runHistoryWith_reindex m M eκ eQ xs)
    (by
      rintro p _ rfl hb
      simpa only [Controller.History.length_snd, Controller.History.map_length,
        configSup_mass_map_reindex] using hb)
    (by rintro p _ rfl hh; simpa [Controller.Halted, last_map_reindex] using hh)
    (by rintro p _ y rfl hy; simpa [last_map_reindex] using hy)

/-- Reindexing preserves `ComputesWithinWith` in both directions. The converse uses `LiftRel.swap`
directly rather than reindexing back by `eκ.symm` and `eQ.symm`, avoiding `[LawfulFunctor F]` (in
particular covering `BinaryChoice`). -/
@[simp] theorem computesWithinWith_reindex_iff [MonadReturns m] [Fintype κ] [Fintype κ']
    (M : StackMachine F κ Γ Q) (eκ : κ ≃ κ') (eQ : Q ≃ Q')
    {xs : List Γ} {outs : m (List Γ)} {t s : ℕ} :
    (M.reindex eκ eQ).ComputesWithinWith m xs outs t s ↔
      M.ComputesWithinWith m xs outs t s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex eκ eQ⟩
  exact of_liftRel_same_output h
    (fun n ↦ (liftRel_runHistoryWith_reindex m M eκ eQ xs n).swap)
    (by
      rintro _ p rfl hb
      simpa only [Controller.History.length_snd, Controller.History.map_length,
        configSup_mass_map_reindex] using hb)
    (by rintro _ p rfl hh; simpa [Controller.Halted, last_map_reindex] using hh)
    (by rintro _ p y rfl hy; simpa [last_map_reindex] using hy)

/-- Reindexing preserves deterministic `ComputesWithin` in both directions. -/
@[simp] theorem computesWithin_reindex_iff [Fintype κ] [Fintype κ']
    (M : StackMachine Id κ Γ Q) (eκ : κ ≃ κ') (eQ : Q ≃ Q') {xs ys : List Γ} {t s : ℕ} :
    (M.reindex eκ eQ).ComputesWithin xs ys t s ↔ M.ComputesWithin xs ys t s :=
  M.computesWithinWith_reindex_iff eκ eQ

end Transfer

end Complexity.StackMachine
