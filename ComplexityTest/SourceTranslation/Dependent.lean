/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Dependent

-- A dependent callback borrows a represented table from its full runtime environment.
example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun p : Σ x : (Σ n, (Fin n → α) × List (Fin n)), Fin x.1 =>
      p.1.2.1 p.2)) := ⟨by source_fun_prop⟩

-- Both indices must survive closure, including the dependency in the result's type.
example : Nonempty (Implementation
    (fun p : Σ x : (Σ n, Σ k, (Fin n → Fin k) × List (Fin n)), Fin x.1 =>
      (p.1.2.2.1 p.2).val)) := ⟨by source_fun_prop⟩

-- Closing the environment cannot turn pointwise implementations into one algorithm.
example (f : ℕ → Bool → Bool) (_h : ∀ n, Implementation (f n)) : True := by
  fail_if_success
    have : Nonempty (Implementation (fun p : Σ x : ℕ × List Bool, Bool => f p.1.1 p.2)) :=
      ⟨by source_fun_prop⟩
  trivial

-- Pure environment extraction must not reproduce itself as a subgoal.
open Lean in
run_elab do
  let fn ← Elab.Term.elabTerm (← `(fun p :
      Σ x : (Σ n, (Fin n → Nat) × List (Fin n)), Fin x.1 =>
    (⟨p.1.1, p.1.2.1, p.2⟩ : Σ n, (Fin n → Nat) × Fin n))) none
  if (← Environment.decomposition? fn).isSome then
    throwError "environment decomposition made no progress"

end ComplexityTest.SourceTranslation.Dependent
