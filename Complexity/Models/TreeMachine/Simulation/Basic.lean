/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Complexity.Models.StackMachine.Program.Basic
public import Complexity.Data.Tree.Encoding
public import Complexity.Control.Program.For

/-! # A tree-register simulator over local stack operations -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation

set_option backward.isDefEq.respectTransparency false in
/-- Temporary stacks restored to empty at each source-step boundary. -/
inductive Scratch where
  | counter
  | saved
  | temp
  deriving DecidableEq, Fintype

/-- Two register banks and three reusable temporary stacks. -/
inductive Work (k : ℕ) where
  | data (bank : Bool) (reg : Fin k)
  | scratch (slot : Scratch)
  deriving DecidableEq, Fintype

@[simp] theorem card_scratch : Fintype.card Scratch = 3 := rfl

@[simp] theorem card_work (k : ℕ) : Fintype.card (Work k) = 2 * k + 3 := by
  rw [← Fintype.card_congr (proxy_equiv% (Work k))]
  simp

namespace Program

open StackMachine.Program Work

variable {k : ℕ} {Q : Type} {xs : Array Bool}

/-- All scratch stacks are empty at source-step boundaries. -/
def contents (b : Bool) (ρ σ : Fin k → List Bool) : Work k → List Bool
  | .data d i => if d = b then ρ i else σ i
  | .scratch _ => []

@[simp] theorem contents_data (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k) :
    contents b ρ σ (data b i) = ρ i := by simp [contents]

@[simp] theorem contents_other (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k) :
    contents b ρ σ (data (!b) i) = σ i := by simp [contents]

@[simp] theorem contents_scratch (b : Bool) (ρ σ : Fin k → List Bool) (i : Scratch) :
    contents b ρ σ (.scratch i) = [] := rfl

theorem contents_swap (b : Bool) (ρ σ : Fin k → List Bool) :
    contents (!b) σ ρ = contents b ρ σ := by
  funext i
  rcases i with ⟨d, i⟩ | i
  · cases b <;> cases d <;> rfl
  · rfl

theorem contents_update_other (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k) (w : List Bool) :
    Function.update (contents b ρ σ) (data (!b) i) w = contents b ρ (Function.update σ i w) := by
  funext j
  rcases j with ⟨d, j⟩ | j
  · cases b <;> cases d <;> simp [contents, Function.update_apply]
  · simp [contents]

/-- Represent both register banks while preserving the external streams. -/
@[simps -fullyApplied]
def bank (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool) : StackMachine.Cfg (Work k) Bool Unit xs :=
  { c with «stacks» := contents b (fun i ↦ BitList.encodeTree (ρ i)) σ }

@[simp] theorem bank_self (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool)
    (h : c.stacks = contents b (fun i ↦ BitList.encodeTree (ρ i)) σ) : bank c b ρ σ = c := by
  simp [bank, ← h]

/-- The first `n` destination registers have been rebuilt. -/
def buffer (σ τ : Fin k → List Bool) (n : ℕ) (i : Fin k) : List Bool :=
  if i.val < n then τ i else σ i

@[simp] theorem buffer_zero (σ τ : Fin k → List Bool) : buffer σ τ 0 = σ := by
  funext i; simp [buffer]

@[simp] theorem buffer_all (σ τ : Fin k → List Bool) : buffer σ τ k = τ := by
  funext i; simp [buffer]

theorem buffer_update (σ τ : Fin k → List Bool) (i : Fin k) :
    Function.update (buffer σ τ i.val) i (τ i) = buffer σ τ (i.val + 1) := by
  funext j
  by_cases h : j = i
  · subst j; simp [buffer]
  · have hj : j.val ≠ i.val := fun he ↦ h (Fin.ext he)
    simp only [Function.update_of_ne h, buffer]
    split_ifs <;> first | rfl | omega

/-- The configuration after rebuilding the first `n` destination registers. -/
def cycle (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) (n : ℕ) :=
  bank c b ρ (buffer σ (fun i ↦ BitList.encodeTree (ν i)) n)

theorem cycle_next (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) (i : Fin k) :
    (cycle c b ρ ν σ i.val).setStack (data (!b) i) (BitList.encodeTree (ν i)) =
      cycle c b ρ ν σ (i.val + 1) := by
  ext j <;> simp [cycle, contents_update_other, buffer_update]

@[simp] theorem cycle_zero (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) : cycle c b ρ ν σ 0 = bank c b ρ σ := by
  simp [cycle]

@[simp] theorem cycle_all (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) :
    cycle c b ρ ν σ k = bank c (!b) ν (fun i ↦ BitList.encodeTree (ρ i)) := by
  simp [cycle, bank, contents_swap]

/-- Observe all register roots in a single local transition. -/
def roots (b : Bool) : StackMachine.Program (Work k) Bool (Fin k → Bool) := do
  let v ← observeBits fun v i ↦ v.2 (data b i) == some true
  pure (fun i ↦ v[i])

end Program
end Complexity.TreeMachine.Simulation
