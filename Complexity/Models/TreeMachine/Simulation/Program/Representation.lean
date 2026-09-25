/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Representation
public import Complexity.Models.TuringMachine.Configuration

/-! # Register-bank assertions independent of a target control graph -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.Program

open Compiler TM.Program.Word

variable {k : ℕ} {xs : Array (Option Bool)}

/-- A partially replaced destination bank. -/
def buffer (σ τ : Fin k → List Bool) (n : ℕ) (i : Fin k) : List Bool :=
  if i.val < n then τ i else σ i

@[simp] theorem buffer_zero (σ τ : Fin k → List Bool) : buffer σ τ 0 = σ := by
  funext i
  simp [buffer]

@[simp] theorem buffer_all (σ τ : Fin k → List Bool) : buffer σ τ k = τ := by
  funext i
  simp [buffer]

theorem buffer_update (σ τ : Fin k → List Bool) (i : Fin k) :
    Function.update (buffer σ τ i.val) i (τ i) = buffer σ τ (i.val + 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [buffer]
  · have h' : j.val ≠ i.val := fun he ↦ h (Fin.ext he)
    simp only [Function.update_of_ne h, buffer]
    have hj : (j.val < i.val + 1) = (j.val < i.val) := propext (by omega)
    simp only [hj]

/-- Data at a source-step boundary; finite control is supplied by the surrounding program. -/
def bankCfg (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool) : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs :=
  { c with workTapes := tapes b (fun i ↦ BitList.encodeTree (ρ i)) σ, workPos := fun _ ↦ 0 }

theorem bankCfg_eq (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool)
    (hw : c.workTapes = tapes b (fun i ↦ BitList.encodeTree (ρ i)) σ)
    (hp : c.workPos = fun _ ↦ 0) :
    bankCfg c b ρ σ = c := by
  simp [bankCfg, ← hw, ← hp]

/-- The configuration after precisely the first `n` destination registers were built. -/
def cycleCfg (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) (n : ℕ) :
    TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs :=
  bankCfg c b ρ (buffer σ (fun i ↦ BitList.encodeTree (ν i)) n)

theorem cycleCfg_next (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) (i : Fin k) :
    { cycleCfg c b ρ ν σ i.val with
      workTapes := Function.update (cycleCfg c b ρ ν σ i.val).workTapes
        (data (!b) i) (tape (BitList.encodeTree (ν i))) } = cycleCfg c b ρ ν σ (i.val + 1) := by
  apply TM.Cfg.ext <;> try rfl
  simp only [cycleCfg, bankCfg, ← tapes_update_other, buffer_update]

theorem cycleCfg_all (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) :
    cycleCfg c b ρ ν σ k = bankCfg c (!b) ν (fun i ↦ BitList.encodeTree (ρ i)) := by
  simp [cycleCfg, bankCfg, tapes_swap]

theorem workSymbols_roots (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool)
    (ht : c.workTapes = tapes b (fun i ↦ BitList.encodeTree (ρ i)) σ)
    (hp : c.workPos = fun _ ↦ 0) :
    (fun i ↦ c.workSymbols (data b i) == some true) = fun i ↦ Tree.root (ρ i) := by
  funext i
  simp only [TM.Cfg.workSymbols, ht, hp, tapes_data]
  change ((tape (BitList.encodeTree (ρ i)))[(0 : ℤ)] == some true) = _
  cases ρ i <;> rfl

end Complexity.TreeMachine.Simulation.Program
