/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity

namespace ComplexityTest.SourceTranslation.Guidance

def userReverse {α : Type*} : List α → List α
  | [] => []
  | x :: xs => userReverse xs ++ [x]

theorem userReverse_eq {α : Type*} : userReverse (α := α) = List.reverse := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [userReverse, ih]

private def reverseByCases (xs : List Bool) := match xs with
  | [] => []
  | x :: xs => (x :: xs).reverse

-- Both entries must simplify the budget by the selected implementation's cases.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace reverseByCases
    (fun n => 30 * n + 40) (fun n => k * (n + 3)) := by model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Bool))
    (fun n => 30 * n + 40) (fun n => k * (n + 3)) := by
  model_fun_prop via reverseByCases
  case source_eq => funext xs; cases xs <;> simp [reverseByCases]

-- An ordinary equality remains as an ordinary tactic goal.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (userReverse (α := Bool))
    (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop via List.reverse
  case source_eq => exact userReverse_eq

section
attribute [local source] userReverse_eq

-- The selected source is reusable under a branch with a captured value.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun x : List α × Option (List α) =>
        match x.2 with | none => x.1 | some xs => userReverse xs)
      (fun n => 30 * n + 40) (fun n => k * (n + 3)) := by
  model_fun_prop
end

-- A local choice does not leak outside its section.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (userReverse (α := Bool))
        (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
      model_fun_prop
  trivial

def retain (xs : List Bool) := xs

-- The explicitly selected slower algorithm cannot be replaced by identity to meet a budget.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
        (fun _ => 4) (fun n => k * (n + 3)) := by
      model_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
      case source_eq => funext xs; simp [retain]
  trivial

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
  case source_eq => funext xs; simp [retain]

section
-- Saving a public budget retains the explicitly chosen, slower program.
@[local source] theorem retain_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
      (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
  case source_eq => funext xs; simp [retain]

example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
        (fun _ => 4) (fun n => k * (n + 3)) := by
      model_fun_prop
  trivial

-- A looser valid bound on that same program remains usable.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
    (fun n => 30 * n + 40) (fun n => k * (n + 3)) := by
  model_fun_prop
end

-- The local model-budget registration ends with its section.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retain
    (fun _ => 4) (fun n => k * (n + 3)) := by
  model_fun_prop

-- Model automation must leave unrelated goals for the caller.
example : (∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (userReverse (α := Bool))
    (fun n => 13 * n + 20) (fun n => k * (n + 3))) ∧ True := by
  constructor
  model_fun_prop via List.reverse
  case source_eq => exact userReverse_eq
  trivial

-- A user-defined interpretation needs only ordinary source and an equality.
namespace ReverseByCases

def userReverse {α : Type*} (xs : List α) := match xs with
  | [] => []
  | x :: xs => xs.reverse ++ [x]

@[scoped source] theorem reverse_eq {α : Type*} :
    List.reverse (α := α) = userReverse := by
  funext xs
  cases xs <;> simp [userReverse]

end ReverseByCases

-- The left-hand function adopts the right-hand implementation, including its case budgets.
theorem customReverse_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := α))
      (fun n => 40 * n + 40) (fun n => k * (2 * n + 10)) := by
  model_fun_prop using ReverseByCases

-- Inspect the selected cost, so silently keeping the built-in reverse cannot pass this test.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, TreeProgram.Source.Realizes (List.reverse (α := α)) b ∧ b.time [] = 5 ∧
      ∀ x xs, b.time (x :: xs) = 39 * xs.length + 33 := by
  refine ⟨_, by source_fun_prop using ReverseByCases, ?_, ?_⟩
  · rfl
  · intros; simp; omega

-- A chosen implementation cannot be exchanged for the cheaper built-in rule to fit a budget.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Bool))
        (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
      model_fun_prop using ReverseByCases
  trivial

-- `using` has the same scope behavior as Lean's ordinary `open scoped`.
open scoped ReverseByCases in
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := α))
      (fun n => 40 * n + 40) (fun n => k * (2 * n + 10)) := by model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Bool))
    (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by model_fun_prop

-- Generic scopes also work with the existing one-off replacement entry.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (userReverse (α := Bool))
    (fun n => 40 * n + 40) (fun n => k * (2 * n + 10)) := by
  model_fun_prop using ReverseByCases via List.reverse
  case source_eq => exact userReverse_eq

def chosenReverse {α : Type*} : List α → List α := List.reverse

-- Save the choice once; callers need neither the scope nor an internal certificate.
@[source using ReverseByCases] theorem chosenReverse_eq {α : Type*} :
    chosenReverse (α := α) = List.reverse := rfl

theorem chosenReverse_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun x : List α × Option (List α) =>
        match x.2 with | none => x.1 | some xs => chosenReverse xs)
      (fun n => 60 * n + 100) (fun n => k * (2 * n + 20)) := by model_fun_prop

attribute [source] userReverse_eq

namespace Scoped
def custom (xs : List Bool) := xs
@[scoped source] theorem custom_eq : custom = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [custom]
end Scoped

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace Scoped.custom
    (fun _ => 4) (fun n => k * (n + 3)) := by model_fun_prop

open scoped Scoped in
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace Scoped.custom
        (fun _ => 4) (fun n => k * (n + 3)) := by model_fun_prop
  trivial

section
@[local source] theorem identity_eq :
    (id : List Bool → List Bool) = (fun xs => xs.reverse.reverse) := by funext xs; simp

example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : List Bool → List Bool)
        (fun _ => 4) (fun n => k * (n + 3)) := by model_fun_prop
  trivial
end

-- Compiling a replacement does not fall back to the already supported original function.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Nat))
        (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
      model_fun_prop via (fun xs : List Nat => xs.map Nat.factorial)
  trivial

theorem conditionalChoice (h : False) : (id : List Bool → List Bool) = List.reverse :=
  False.elim h

/-- error: `source` needs an unconditional function equality; use a local `via` proof for a replacement depending on a hypothesis -/
#guard_msgs in
attribute [source] conditionalChoice

def unregisteredReverse : List Bool → List Bool
  | [] => []
  | x :: xs => unregisteredReverse xs ++ [x]

theorem unsupportedChoice : (List.reverse : List Bool → List Bool) = unregisteredReverse := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [unregisteredReverse, ← ih]

/-- error: source translation: `ComplexityTest.SourceTranslation.Guidance.unregisteredReverse` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`) -/
#guard_msgs in
attribute [source] unsupportedChoice

open Lean Elab Command in
run_elab do
  let env ← getEnv
  if env.constants.fold (init := false) (fun found name _ => found ||
      (`ComplexityTest.SourceTranslation.Guidance.unsupportedChoice.sourceImplementation).isPrefixOf name) then
    throwError "a failed source registration left a partial certificate"

end ComplexityTest.SourceTranslation.Guidance
