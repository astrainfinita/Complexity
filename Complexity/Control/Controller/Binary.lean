/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice.Basic
public import Complexity.Control.Controller.Execution
public import Complexity.Control.Controller.RunHistory

/-!
# Deterministic controllers as binary choices

Duplicating each deterministic action preserves reachable configurations.
The multiset interpretation retains the multiplicity of coincident paths.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {Observation : Type*} {Action Config : Type u} {Q : Type*}
variable (M : Controller Id Observation Action Q)
  [HasState Config Q]

/-- Embed a deterministic controller by giving both branch indices its unique action. -/
def toBinary : Controller BinaryChoice Observation Action Q where
  q₀ := M.q₀
  halt := M.halt
  transition q a _ := (M.transition q a).run

/-- Embedding a deterministic controller preserves its halting test. -/
@[simp] theorem halted_toBinary_iff (c : Config) :
    M.toBinary.Halted c ↔ M.Halted c := Iff.rfl

variable {Input Output : Type*}

/-- Duplicating transitions preserves the standard input configuration. -/
@[simp] theorem initInput_toBinary (input : Input)
    [Execution Config Q Output input] :
    M.toBinary.initInput (Config := Config) input = M.initInput input := rfl

variable [Observe Config Observation] [Apply Config Action]

/-- Both alternatives of an embedded deterministic step have the original successor. -/
@[simp] theorem mem_stepWith_toBinary_iff (c d : Config) :
    d ∈ M.toBinary.stepWith Multiset c ↔
      d = M.step c := by
  by_cases h : M.halt (state c) = true <;>
    simp [step, stepWith, toBinary, h]

/-- Embedding retains exactly the deterministic endpoint, possibly with several paths. -/
@[simp] theorem mem_runFromWith_toBinary_iff (c d : Config) (n : ℕ) :
    d ∈ M.toBinary.runFromWith Multiset c n ↔
      d = M.runFrom c n := by
  induction n generalizing c with
  | zero => exact Multiset.mem_singleton
  | succ n ih =>
    simp only [runFromWith_succ, runFrom_succ, Multiset.bind_def, Multiset.mem_bind,
      mem_stepWith_toBinary_iff, ih, exists_eq_left]

/-- Standard input execution reaches exactly the original deterministic endpoint. -/
@[simp] theorem mem_runWith_toBinary_iff (input : Input) (d : Config) (n : ℕ)
    [Execution Config Q Output input] :
    d ∈ M.toBinary.runWith Config Multiset input n ↔ d = M.run Config input n :=
  M.mem_runFromWith_toBinary_iff (M.initInput input) d n

/-- Duplicated deterministic choices record exactly the original action history. -/
theorem mem_runHistoryFromWith_toBinary_iff (c : Config)
    (h : History Config Action) (n : ℕ) :
    h ∈ M.toBinary.runHistoryFromWith Multiset c n ↔ h = M.runHistoryFrom c n :=
  M.mem_runFromWith_toBinary_iff (History.nil c) h n

/-- Duplicated deterministic choices preserve standard-input histories. -/
theorem mem_runHistoryWith_toBinary_iff (input : Input) (h : History Config Action) (n : ℕ)
    [Execution Config Q Output input] :
    h ∈ M.toBinary.runHistoryWith Config Multiset input n ↔ h = M.runHistory Config input n :=
  M.mem_runHistoryFromWith_toBinary_iff (M.initInput input) h n

end Complexity.Controller
