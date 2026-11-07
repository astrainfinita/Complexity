/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgram)
namespace ComplexityTest.SourceTranslation.Dependent

-- A dependent callback borrows a represented table from its full runtime environment.
example {α : Type*} [UniqueEncoding Tree α] :=
  (by source_fun_prop : HasProgram (fun p : Σ x : (Σ n, (Fin n → α) × List (Fin n)), Fin x.1 =>
    p.1.2.1 p.2) _ _ _)

-- Both indices must survive closure, including the dependency in the result's type.
example := (by source_fun_prop : HasProgram
    (fun p : Σ x : (Σ n, Σ k, (Fin n → Fin k) × List (Fin n)), Fin x.1 =>
      (p.1.2.2.1 p.2).val) _ _ _)

-- Closing the environment cannot turn pointwise implementations into one algorithm.
example (f : ℕ → Bool → Bool) (program : ℕ → Value → Code Value) (t p : ℕ → Bool → ℕ)
    (_h : ∀ n, HasProgram (f n) (program n) (t n) (p n)) : True := by
  fail_if_success
    have := (by source_fun_prop : HasProgram (fun p : Σ x : ℕ × List Bool, Bool => f p.1.1 p.2)
      _ (fun _ => 1) (fun _ => 1))
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
