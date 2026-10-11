/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import ComplexityTest.SourceTranslation.Guidance

-- The existing built-in scope needs no namespace-opening command.
example : ∃ k, Complexity.TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Bool))
    (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by model_fun_prop using tabulate

open Complexity

namespace ComplexityTest.SourceTranslation.Public

-- Recursive mathematical bounds stay as ordinary goals for user induction.
theorem recursiveTimeBound_model (m : Nat) :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : Bool → Bool)
      (fun _ => Nat.rec 10 (fun _ r => 2 * r) m) (fun n => k * (n + 3)) := by
  model_fun_prop
  guard_target = 4 ≤ Nat.rec 10 (fun _ r => 2 * r) m
  induction m with
  | zero => decide
  | succ m ih =>
    change 4 ≤ 2 * Nat.rec 10 (fun _ r => 2 * r) m
    omega

example (m : Nat) : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : Bool → Bool)
    (fun _ => 4) (fun n => k * (n + Nat.rec 10 (fun _ r => 2 * r) m)) := by
  model_fun_prop
  guard_target = 2 ≤ Nat.rec 10 (fun _ r => 2 * r) m
  induction m with
  | zero => decide
  | succ m ih =>
    change 2 ≤ 2 * Nat.rec 10 (fun _ r => 2 * r) m
    omega

-- Returning a cost-shaped pair does not make genuine recursion a finite case split.
example (m : Nat) : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : Bool → Bool)
    (fun _ => (Nat.rec (motive := fun _ => Nat × Nat) (10, 10)
      (fun _ r => (2 * r.1, 2 * r.2)) m).1) (fun n => k * (n + 3)) := by
  model_fun_prop
  guard_target = 4 ≤ (Nat.rec (motive := fun _ => Nat × Nat) (10, 10)
    (fun _ r => (2 * r.1, 2 * r.2)) m).1
  induction m with
  | zero => decide
  | succ m ih =>
    change 4 ≤ 2 * (Nat.rec (motive := fun _ => Nat × Nat) (10, 10)
      (fun _ r => (2 * r.1, 2 * r.2)) m).1
    omega

-- Simplify saved finite case costs even when the user's upper bound is recursive.
example (m : Nat) : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := Bool))
    (fun n => 40 * (n - 1) + Nat.rec 40 (fun _ r => 2 * r) m)
    (fun n => k * (2 * n + 10)) := by
  model_fun_prop using Guidance.ReverseByCases
  guard_target = 9 ≤ Nat.rec 40 (fun _ r => 2 * r) m
  induction m with
  | zero => decide
  | succ m ih =>
    change 9 ≤ 2 * Nat.rec 40 (fun _ r => 2 * r) m
    omega

-- An ordinary function equality supplies the reusable implementation across modules.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun xs : List Bool => some (Guidance.userReverse xs))
    (fun n => 13 * n + 25) (fun n => k * (n + 5)) := by
  model_fun_prop
  simp [Guidance.userReverse_eq, Nat.add_comm]

-- A saved user choice retains its implementation under nested calls across modules.
theorem registeredChoice_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun xs : List α => some (Guidance.chosenReverse xs))
      (fun n => 50 * n + 60) (fun n => k * (2 * n + 20)) := by
  model_fun_prop
  simp [Guidance.chosenReverse_eq]
  omega

example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (Guidance.chosenReverse (α := Bool))
        (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by model_fun_prop
  trivial

-- User-defined scoped interpretations are also selectable by an importing module.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.reverse (α := α))
      (fun n => 40 * n + 40) (fun n => k * (2 * n + 10)) := by
  model_fun_prop using Guidance.ReverseByCases

-- No internal namespace, implementation object or rule-registration list is needed.
def twice (xs : List Bool) := xs.reverse.reverse

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace twice
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun x : Option (List Bool) => match x with | none => [] | some xs => xs.reverse)
    (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

-- Callback budgets add per element, even when one list is long and the others are empty.
def reverseLast (x : List Unit × List (List Unit)) : List Unit :=
  x.2.foldl (fun _ ys => ys.reverse) x.1

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace reverseLast
    (fun n => 22 * n + 14) (fun n => k * (n + 2)) := by
  model_fun_prop
  · rename_i x
    rcases x with ⟨a, xs⟩
    have h := List.sum_le_sum (l := xs)
      (fun ys _ => TreeProgram.Source.length_le_codeSize ys)
    rw [List.sum_map_mul_left, size_encode_prod, size_encode_list xs]
    dsimp only at h ⊢
    omega
  · rename_i x
    rcases x with ⟨a, xs⟩
    refine (TreeProgram.Source.foldlCost_peak_le _ _ ?_ ?_).trans ?_
    · intros; simp
    · intros; simp
    · simp only [size_encode_prod]; omega

end ComplexityTest.SourceTranslation.Public
