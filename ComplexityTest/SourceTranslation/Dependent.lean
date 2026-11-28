/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
namespace ComplexityTest.SourceTranslation.Dependent

-- A dependent callback borrows a represented vector from its full runtime environment.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgramInO
    (fun p : Σ x : (Σ n, FinVector α n × List (Fin n)), Fin x.1 => p.1.2.1.get p.2) _ _ _)

-- Both indices must survive closure, including the dependency in the result's type.
example := (by source_fun_prop : HasProgramInO
    (fun p : Σ x : (Σ n, Σ k, FinVector (Fin k) n × List (Fin n)), Fin x.1 =>
      (p.1.2.2.1.get p.2).val) _ _ _)

-- Polymorphic operations on `Option` compose across a dependent element type.
example := (by source_fun_prop : HasProgramInO (fun x : Σ n, Option (Fin n) => someValue x.2) _ _ _)

-- Guards closed-index `FinVector` projection (`encode_finVector_get_apply` in `O(1)`) and dynamic
-- `FinVector` lookup (`encode_finVector_get_eq_someValue` at `low` priority).
example : HasProgramIn (fun x : Σ n, FinVector (Fin n) 1 => (x.2.get 0).val) hole(⊢ p)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole p using programFinVectorClosedGetGuard
  fill_hole p in source_fun_prop

example : HasProgramIn (fun x : Σ n, Σ m, FinVector (Fin m) n × Fin n =>
    (x.2.2.1.get x.2.2.2).val) hole(⊢ p) IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole p using programFinVectorDynamicGetGuard
  fill_hole p in source_fun_prop

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

-- Guards the view `Fin.val_natAdd`: the value of a shifted index is a sum of numbers.
example := (by source_fun_prop : HasProgramInO shiftWire _ _ _)

-- A selected implementation of a definition with a `source_view` rewrite is not bypassed by
-- `assembly?` inside a constructor (including after a `source_view` rewrite step).
private def opaqueFinVec {n : ℕ} (v : FinVector (Fin n) n) : FinVector (Fin n) n := v

private theorem encode_opaqueFinVec {n : ℕ} (v : FinVector (Fin n) n) :
    ⌜opaqueFinVec v⌝ₜ = ⌜v⌝ₜ := rfl

attribute [local source_view, local dominated_expand] encode_opaqueFinVec in
example (q : Value → Code Value)
    (h : HasProgramInO (fun x : Σ n, FinVector (Fin n) n => opaqueFinVec x.2) q
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size)) :
    HasProgramIn (fun x : Σ n, FinVector (Fin n) n =>
      (⟨x.1, (opaqueFinVec x.2).map Fin.castSucc⟩ : Σ n, FinVector (Fin (n + 1)) n))
      (fun v => do
        let a ← Code.eval (v.expression.subtree [false])
        let b ← q v
        Code.eval (.pair a.expression b.expression))
      IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop

attribute [local source_view, local dominated_expand] encode_opaqueFinVec in
example (q : Value → Code Value)
    (_h : HasProgramInO (fun x : Σ n, FinVector (Fin n) n => opaqueFinVec x.2) q
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size)) : True := by
  fail_if_success
    have : HasProgramIn (fun x : Σ n, FinVector (Fin n) n =>
        (⟨x.1, (opaqueFinVec x.2).map Fin.castSucc⟩ : Σ n, FinVector (Fin (n + 1)) n))
        (fun v => Code.eval (.pair (v.expression.subtree [false])
          (v.expression.subtree [true])))
        IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
      source_fun_prop
  trivial

-- Closing the environment cannot turn pointwise implementations into one algorithm.
example (f : ℕ → Bool → Bool) (program : ℕ → Value → Code Value) (t p : ℕ → Bool → ℕ)
    (_h : ∀ n, HasProgramInO (f n) (program n) (t n) (p n)) : True := by
  fail_if_success
    have := (by source_fun_prop : HasProgramInO (fun p : Σ x : ℕ × List Bool, Bool => f p.1.1 p.2)
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
