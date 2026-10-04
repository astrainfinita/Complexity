/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Complexity.Models.StackMachine.Program.Basic
public import Complexity.Data.Tree.Encoding
public import Complexity.Models.TreeMachine.Cost

/-! # A tree-register simulator over local stack operations -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation

set_option backward.isDefEq.respectTransparency false in
/-- Temporary stacks restored to empty at each source-step boundary. -/
inductive Scratch where
  | counter
  | saved
  | temp
  | result
  deriving DecidableEq, Fintype

/-- One stack per register and four reusable temporary stacks. -/
inductive Work (k : ℕ) where
  | data (reg : Fin k)
  | scratch (slot : Scratch)
  deriving DecidableEq, Fintype

@[simp] theorem card_scratch : Fintype.card Scratch = 4 := rfl

@[simp] theorem card_work (k : ℕ) : Fintype.card (Work k) = k + 4 := by
  rw [← Fintype.card_congr (proxy_equiv% (Work k))]
  simp

namespace Program

open StackMachine.Program Work

variable {k : ℕ} {xs : Array Bool}

/-- Scratch is empty between source instructions. -/
def contents (ρ : Fin k → Tree) : Work k → List Bool
  | .data i => BitList.encodeTree (ρ i)
  | .scratch _ => []

@[simp] theorem contents_data (ρ : Fin k → Tree) (i : Fin k) :
    contents ρ (data i) = BitList.encodeTree (ρ i) := rfl

@[simp] theorem contents_scratch (ρ : Fin k → Tree) (i : Scratch) :
    contents ρ (.scratch i) = [] := rfl

/-- Represent the register bank while preserving external streams. -/
@[simps -fullyApplied]
def bank (c : StackMachine.Cfg (Work k) Bool Unit xs) (ρ : Fin k → Tree) :
    StackMachine.Cfg (Work k) Bool Unit xs :=
  { c with «stacks» := contents ρ }

@[simp] theorem bank_self (c : StackMachine.Cfg (Work k) Bool Unit xs)
    (ρ : Fin k → Tree) (h : c.stacks = contents ρ) : bank c ρ = c := by
  simp [bank, ← h]

@[simp] theorem bank_bank (c : StackMachine.Cfg (Work k) Bool Unit xs)
    (ρ ν : Fin k → Tree) : bank (bank c ρ) ν = bank c ν := rfl

/-- Observe all register roots in a single local transition. -/
def roots : StackMachine.Program (Work k) Bool (Fin k → Bool) := do
  let v ← observeBits fun v i ↦ v.2 (data i) == some true
  pure (fun i ↦ v[i])

end Program
end Complexity.TreeMachine.Simulation
