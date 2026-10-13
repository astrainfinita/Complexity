/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity
namespace ComplexityTest.SourceTranslation.TailRecursion

open Lean Meta Elab Tactic in
elab (name := guardTailGoals) "guard_tail_goals" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if (target.find? fun e => e.isAppOf ``TreeProgram.Source.Bounds.time ||
          e.isAppOf ``TreeProgram.Source.Bounds.peak || match e with
            | .proj ``TreeProgram.Source.Bounds _ _ => true
            | _ => false).isSome then
        throwError "tail loop left a budget field projection in a local obligation"
      if (target.find? fun e => e.isApp && e.getAppFn.isLambda).isSome then
        throwError "tail loop left a beta redex in a local obligation"
      let displayed := (← ppExpr target).pretty
      if (displayed.splitOn "TreeProgram.Source").length > 1 then
        throwError "tail loop exposed an internal certificate or budget projection"

#allow_unused_tactic! guardTailGoals

def gather : Bool × List (List Bool) × List Bool → List Bool
  | (_, [], acc) => acc
  | (tag, xs :: rest, acc) => gather (tag, rest, tag :: tag :: (xs.reverse ++ acc))
termination_by x => x.2.1.length

def advance (x : Bool × List (List Bool) × List Bool) :=
  match x.2.1 with
  | [] => x
  | xs :: rest => (x.1, rest, x.1 :: x.1 :: (xs.reverse ++ x.2.2))

-- This is a remaining-time estimate, not a declaration of exact callback costs.
-- Its definition uses the list's structural termination proof.
def credit : List (List Bool) → ℕ
  | [] => 200
  | xs :: rest => 100 * (⌜xs⌝ₜ.size + 1) + credit rest

theorem credit_le (xs : List (List Bool)) : credit xs ≤ 100 * ⌜xs⌝ₜ.size + 100 := by
  induction xs with
  | nil => simp [credit]
  | cons xs rest ih => simp only [credit, encode_list_cons, size_encode_prod]; omega

@[scoped source] theorem gather_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace gather
    (fun n => 300 * n + 300) (fun n => k * (20 * n + 20)) := by
  model_fun_prop using loop
    (test := fun x : Bool × List (List Bool) × List Bool => !x.2.1.isEmpty)
    (next := advance) (finish := fun x => x.2.2)
    (invariant := fun x y => ⌜y⌝ₜ.size + 10 * y.2.1.length ≤ ⌜x⌝ₜ.size + 10 * x.2.1.length)
    (time := fun _ y => credit y.2.1)
    (space := fun x => 20 * ⌜x⌝ₜ.size + 18)
  guard_tail_goals
  case equation =>
    rintro ⟨tag, xs, acc⟩
    cases xs <;> simp [gather, advance]
  case initial => intro x; exact le_rfl
  case input_size =>
    rintro ⟨xt, xs, xa⟩ ⟨yt, ys, ya⟩ hi _
    have := TreeProgram.Source.length_le_codeSize xs
    simp at hi ⊢
    omega
  case check_space =>
    rintro ⟨xt, xs, xa⟩ ⟨yt, ys, ya⟩ hi _
    have := TreeProgram.Source.length_le_codeSize xs
    cases ys <;> simp at hi ⊢ <;> omega
  case stop_bounds =>
    rintro ⟨xt, xs, xa⟩ ⟨yt, ys, ya⟩ hi _ h
    have := TreeProgram.Source.length_le_codeSize xs
    simp at h
    subst ys
    simp [credit] at hi ⊢
    omega
  case step_bounds =>
    rintro ⟨xt, original, initial⟩ ⟨tag, ys, acc⟩ hi _ h
    cases ys with
    | nil => simp at h
    | cons xs rest =>
      have := TreeProgram.Source.length_le_codeSize original
      have := TreeProgram.Source.length_le_codeSize xs
      have ha := size_encode_list_append xs.reverse acc
      simp only [TreeProgram.Source.size_encode_reverse] at ha
      dsimp only [advance, credit] at *
      cases tag <;> simp only [size_encode_prod, encode_bool_false, encode_bool_true,
        encode_list_cons, size_encode_unit, List.length_cons,
        List.length_reverse, TreeProgram.Source.size_encode_reverse, max_le_iff] at hi ⊢
      all_goals (repeat' apply And.intro) <;> omega
  case hb.left =>
    rename_i x
    have h := credit_le x.2.1
    rcases x with ⟨tag, xs, acc⟩
    simp only [size_encode_prod] at h ⊢
    omega

-- The accumulator really grows; no decreasing-space condition is hidden in the interface.
example : ⌜((true, [[]], []) : Bool × List (List Bool) × List Bool)⌝ₜ.size <
    ⌜advance (true, [[]], [])⌝ₜ.size := by decide

-- Different chunk lengths produce different certified per-round costs.
open TreeProgram.Source in
example : ∃ b, Realizes advance b ∧
    b.time (true, [[]], []) < b.time (true, [[true]], []) := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

def keep (xs : List Bool) := xs

-- The ordinary implementation would meet time 4 before a loop is selected.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
    (fun _ => 4) (fun n => k * (n + 2)) := by model_fun_prop

@[scoped source] theorem keep_loop_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
      (fun _ => 11) (fun n => k * (n + 2)) := by
  model_fun_prop using loop
    (test := fun _ => false) (next := id) (finish := id)
    (invariant := fun x y => y = x)
    (time := fun _ _ => 2) (space := fun x => ⌜x⌝ₜ.size)
  guard_tail_goals
  all_goals simp_all [keep]

-- The selected loop cannot meet time 4, even though the identity program could.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
        (fun _ => 4) (fun n => k * (n + 2)) := by model_fun_prop
  trivial

-- Another valid budget for that same program remains usable.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
    (fun _ => 15) (fun n => k * (n + 2)) := by model_fun_prop

-- Insufficient remaining credit is rejected at the local stop condition too.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : List Bool → List Bool)
        (fun _ => 11) (fun n => k * (n + 2)) := by
      model_fun_prop using loop
        (test := fun _ => false) (next := id) (finish := id)
        (invariant := fun x y => y = x)
        (time := fun _ _ => 0) (space := fun x => ⌜x⌝ₜ.size)
      all_goals simp_all
  trivial

-- Applying a pointwise estimate keeps the selected callback. An identity-program
-- estimate cannot replace the reverse callback, even in a loop that never advances.
open TreeProgram.Source in
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : List Bool → List Bool)
    (fun _ => 11) (fun n => k * (n + 2)) := by
  let next := Implementation.reverse (α := Bool)
  have next_bound (xs : List Bool) :
      next.bounds.time xs ≤ 13 * xs.length + 9 ∧ next.bounds.peak xs ≤ ⌜xs⌝ₜ.size + 1 := by
    simp [next, reverseBounds]
  have other_bound (xs : List Bool) :
      (Implementation.identity (α := List Bool)).bounds.time xs ≤ 0 ∧
        (Implementation.identity (α := List Bool)).bounds.peak xs ≤ 0 := by simp
  fail_if_success
    model_fun_prop using loop
      (test := fun _ => false) (next := List.reverse) (finish := id)
      (invariant := fun x y => y = x)
      (time := fun _ _ => 2) (space := fun x => ⌜x⌝ₜ.size)
      (next_bound := other_bound)
  model_fun_prop using loop
    (test := fun _ => false) (next := List.reverse) (finish := id)
    (invariant := fun x y => y = x)
    (time := fun _ _ => 2) (space := fun x => ⌜x⌝ₜ.size)
    (next_bound := next_bound)
  guard_tail_goals
  all_goals simp_all

end ComplexityTest.SourceTranslation.TailRecursion
