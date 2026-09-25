/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Execution

/-!
# Deterministic controllers as binary choices

Duplicating each deterministic action gives a binary controller with the same reachable
configurations and traces. Its multiset interpretation retains the multiplicity of coincident paths.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {Observation : Type*} {Action Config : Type u} {Q : Type*}
variable (M : Controller Id Observation Action Q)
  [HasState Config Q]

/-- Embed a deterministic controller by giving both branch indices its unique action. -/
def toBinary : Controller Choice.Binary Observation Action Q where
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
    d ∈ M.toBinary.stepWith Choice.binaryMultiset c ↔
      d = M.step c := by
  by_cases h : M.halt (state c) = true <;>
    simp [step, stepWith, toBinary, h, Choice.binaryMultiset, Choice.Interpretation.id]

/-- Embedding retains exactly the deterministic endpoint, possibly with several paths. -/
@[simp] theorem mem_runFromWith_toBinary_iff (c d : Config) (n : ℕ) :
    d ∈ M.toBinary.runFromWith Choice.binaryMultiset c n ↔
      d = M.runFrom c n := by
  induction n generalizing c with
  | zero => exact Multiset.mem_singleton
  | succ n ih =>
    rw [runFromWith_succ, runFrom_succ]
    change d ∈ (M.toBinary.stepWith Choice.binaryMultiset c).bind
      (fun b => M.toBinary.runFromWith Choice.binaryMultiset b n) ↔
      d = M.runFrom (M.step c) n
    simp only [Multiset.mem_bind, mem_stepWith_toBinary_iff, ih, exists_eq_left]

/-- Every trace of an embedded deterministic controller is its original trace. -/
@[simp] theorem mem_runTraceWith_toBinary_iff (c : Config) (cs : List Config) (n : ℕ) :
    cs ∈ M.toBinary.runTraceWith Choice.binaryMultiset c n ↔
      cs = M.runTrace c n := by
  induction n generalizing c cs with
  | zero => exact Multiset.mem_singleton
  | succ n ih =>
    change cs ∈ (M.toBinary.stepWith Choice.binaryMultiset c).bind
      (fun d => (M.toBinary.runTraceWith Choice.binaryMultiset d n).bind
        (fun ds => {c :: ds})) ↔
      cs = c :: M.runTrace (M.step c) n
    simp only [Multiset.mem_bind, Multiset.mem_singleton, mem_stepWith_toBinary_iff, ih,
      exists_eq_left]

/-- Standard input execution reaches exactly the original deterministic endpoint. -/
@[simp] theorem mem_runWith_toBinary_iff (input : Input) (d : Config) (n : ℕ)
    [Execution Config Q Output input] :
    d ∈ M.toBinary.runWith Choice.binaryMultiset input n ↔ d = M.run input n :=
  M.mem_runFromWith_toBinary_iff (M.initInput input) d n

end Complexity.Controller
