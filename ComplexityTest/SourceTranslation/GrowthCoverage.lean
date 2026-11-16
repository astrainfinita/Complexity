/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

/-! # Growths made of steps, construct by construct

For each construct whose growth is made of the growths of its steps, the simplest use, stated with
`IsPoly` in the code size and, where there is a natural exact bound, with that bound. A use closed
by `fill_hole program in source_fun_prop` alone guards that the translation settles its growth;
a use that is not records the limit and its plan item. Folds and maps are covered in `Traversal`
(`FoldGrowth`, `MapGrowth`), iterations in `Iteration` (`IterateGrowth`). Tail loops and stack
recursion are not here: they take an invariant or a scale from the user with `using loop` and
`using recursion` (tests `TailRecursion`, `AsymptoticTailRecursion`, `Recursion`), and the growth
of a stack recursion has no rule that settles it (plan W83). -/

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.GrowthCoverage

section Fold

-- A fold whose callback captures nothing and keeps a state of bounded size: polynomial, and
-- linear in time and peak. The captured forms are in `Traversal` (`FoldGrowth`), with the limit
-- on explicit time bounds of higher degree.
example : HasProgramIn (fun xs : List ℕ => xs.foldl (fun b u => b || u == 0) false)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn (fun xs : List ℕ => xs.foldl (fun b u => b || u == 0) false)
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

end Fold

section Branch

-- A condition on the input: the growth is an `if` on it, split by cases. Guards the cases of
-- `dominated` on a polynomial statement, with a traversal in a branch.
example : HasProgramIn
    (fun x : Bool × List (List ℕ) => if x.1 then x.2.map List.reverse else x.2)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Linear branches give a linear growth, compared pointwise.
example : HasProgramIn (fun x : Bool × List ℕ => if x.1 then x.2.reverse else x.2)
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Records a limit: against a linear bound, `dominated` splits an `if` by cases only against a power
-- of degree at least 2, so a traversal in a branch, linear itself, is left to the user (plan W76,
-- item 2). The user splits the condition by `Dominated.ite`; this proof should go when `if` is
-- split for both kinds of goal.
example : HasProgramIn
    (fun x : Bool × List (List ℕ) => if x.1 then x.2.map List.reverse else x.2)
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated
  all_goals
    refine (Dominated.ite (g := fun x => ⌜x⌝ₜ.size) (g' := fun x => ⌜x⌝ₜ.size) ?_ ?_
      (fun x : Bool × List (List ℕ) => x.1 = true)).mono fun x => by split <;> rfl
  all_goals dominated

def headReverse : List (List ℕ) → List ℕ
  | [] => []
  | xs :: _ => xs.reverse

-- A `match` whose branches have linear growths: the growth is a `match` on the input, compared
-- pointwise by cases.
example : HasProgramIn headReverse hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size)
    (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn headReverse hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size)
    IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

def tailReverses : List (List ℕ) → List (List ℕ)
  | [] => []
  | _ :: xss => xss.map List.reverse

-- Records a limit: a `match` on a pattern is compared pointwise only, so a traversal in a branch
-- is not settled, polynomial or linear (plan W2, the branch rule for `match`).
example : True := by
  fail_if_success
    have : HasProgramIn tailReverses hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size)
        (IsPoly fun x => ⌜x⌝ₜ.size) := by
      fill_hole program in source_fun_prop
  trivial

end Branch

section Table

-- Records a limit: a tabulated table has its time settled, a sum over the table, but its peak
-- holds the code of the table, which has no rule (plan W82).
example : True := by
  fail_if_success
    have : HasProgramIn (fun x : Σ n, Fin n → Bool => Vector.ofFn (fun i => !x.2 i))
        hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
      fill_hole program in source_fun_prop using tabulate
  trivial

-- Reading a stored table at a stored index: polynomial, and within the square of the code.
example : HasProgramIn (fun x : Σ n, (Fin n → ℕ) × Fin n => x.2.1 x.2.2) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn (fun x : Σ n, (Fin n → ℕ) × Fin n => x.2.1 x.2.2) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  fill_hole program in source_fun_prop

end Table

section Library

-- Library functions implemented by loops have closed growths: a lookup in a list and a range of
-- the length of a list compose without the user, within the square of the code.
example : HasProgramIn (fun x : List ℕ × ℕ => x.1[x.2]?) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn (fun xs : List ℕ => List.range xs.length) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  fill_hole program in source_fun_prop

-- Records a limit: the code of a computed number is not known from the program that computes
-- it, so a sum used again is left to the user (plan W84; the mechanism is that of W69, the code
-- size of intermediate values).
example : True := by
  fail_if_success
    have : HasProgramIn (fun x : ℕ × ℕ => x.1 + x.2 + x.1) hole(⊢ program)
        (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
      fill_hole program in source_fun_prop
  trivial

end Library

end ComplexityTest.SourceTranslation.GrowthCoverage
