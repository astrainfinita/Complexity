/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.GrowthTactic

-- Sums are split; constants use the positivity of the target; fields are bounded by the input.
example : Dominated (fun x : List Bool × List Bool => 1 + ⌜x.2⌝ₜ.size + (x.2.reverse.length + 1))
    (fun x => ⌜x⌝ₜ.size) := by dominated

-- A coefficient is found without being written by the user.
example : Dominated (fun xs : List Bool => ⌜(xs, xs.reverse, xs)⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated

def chunkWork (x : Bool × List (List Bool) × List Bool) : ℕ :=
  match x.2.1 with | [] => 1 | xs :: _ => ⌜xs⌝ₜ.size + 1

def advance (x : Bool × List (List Bool) × List Bool) :=
  match x.2.1 with
  | [] => x
  | xs :: rest => (x.1, rest, x.1 :: x.1 :: (xs.reverse ++ x.2.2))

-- Generated growth follows the source cases; the target is unfolded on request.
example : Implementation advance chunkWork (fun x => ⌜x⌝ₜ.size + 10) := by
  source_fun_prop
  all_goals dominated [chunkWork]

-- A genuine fact about the source function is supplied as a hypothesis and composed.
example (f : List Bool → List Bool)
    (hf : Dominated (fun xs => ⌜f xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size)) :
    Dominated (fun x : Bool × List Bool => ⌜f x.2⌝ₜ.size + 1) (fun x => ⌜x⌝ₜ.size) := by
  have h : Dominated (fun x : Bool × List Bool => ⌜f x.2⌝ₜ.size) (fun x => ⌜x.2⌝ₜ.size) :=
    hf.comp Prod.snd
  dominated

-- A hypothesis about the outer input is used for the elements of a traversal.
example (f : List Bool → ℕ) (hf : Dominated f (fun xs => ⌜xs⌝ₜ.size)) :
    Dominated (fun xs : List Bool =>
      (List.finRange xs.length).foldr (fun i s => max (f xs + ⌜i.val⌝ₜ.size) s) 0)
      (fun xs => ⌜xs⌝ₜ.size) := by
  dominated

-- A maximum over a list is compared element by element, using membership.
example : Dominated (fun x : Bool × List Unit =>
    x.2.foldr (fun y s => max (1 + ⌜x⌝ₜ.size + ⌜y⌝ₜ.size) s) 0) (fun x => ⌜x⌝ₜ.size) := by
  dominated

-- A false comparison is left open rather than closed.
example : True := by
  fail_if_success
    have : Dominated (fun xs : List Bool => ⌜xs⌝ₜ.size * ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
      dominated
      done
  trivial

-- The target is never changed: an unprovable summand remains against the same target.
example (g : List Bool → ℕ) (hg : ∀ xs, 0 < g xs) (hle : ∀ xs, xs.length ≤ g xs) :
    Dominated (fun xs : List Bool => 1 + xs.length) g := by
  dominated
  guard_target = Dominated (fun xs : List Bool => xs.length) g
  exact Dominated.of_le hle

-- The right side is not rewritten, even where its encoded sizes could be expanded.
example (f : List Bool → ℕ) (hf : ∀ xs, f xs ≤ ⌜(xs, xs)⌝ₜ.size) :
    Dominated (fun xs : List Bool => 1 + f xs) (fun xs => ⌜(xs, xs)⌝ₜ.size) := by
  dominated
  guard_target = Dominated (fun xs : List Bool => f xs) (fun xs => ⌜(xs, xs)⌝ₜ.size)
  exact Dominated.of_le hf

-- Powers are compared through their bases, with a coefficient on the base.
example : Dominated (fun x : ℕ × ℕ => (2 * x.1 + x.2 + 1) ^ 3) (fun x => (x.1 + x.2 + 1) ^ 3) := by
  dominated

/-- Named fields of a derived structure. -/
@[tree_encoding]
structure Pair where
  /-- The first list. -/
  first : List Bool
  /-- The second list. -/
  second : List Bool

-- A derived structure input is split into its fields.
example : Dominated (fun x : Pair => ⌜x.first⌝ₜ.size + x.second.length) (fun x => ⌜x⌝ₜ.size) := by
  dominated

-- A table sum is bounded entry by entry, each entry multiplied by the table length.
example : Dominated (fun n : ℕ => ((List.finRange n).map fun i : Fin n => ⌜(i : ℕ)⌝ₜ.size).sum)
    (fun n => (n + 1) ^ 2) := by
  dominated

end ComplexityTest.SourceTranslation.GrowthTactic
