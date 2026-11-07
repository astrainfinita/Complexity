/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgram)

namespace ComplexityTest.SourceTranslation.GrowthTactic

-- Sums are split; constants use the positivity of the target; fields are bounded by the input.
example : Dominated (fun x : List Bool × List Bool => 1 + ⌜x.2⌝ₜ.size + (x.2.reverse.length + 1))
    (fun x => ⌜x⌝ₜ.size) := by dominated

-- A difference equal to the target is compared as stated, before its minuend.
example : Dominated (fun xs : List Bool => ⌜xs⌝ₜ.size - 1) (fun xs => ⌜xs⌝ₜ.size - 1) := by
  dominated

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
example : HasProgram advance hole(⊢ program) chunkWork (fun x => ⌜x⌝ₜ.size + 10) := by
  fill_hole program in source_fun_prop (disch := dominated [chunkWork])

-- A statement in the list is instantiated at the matching terms of the pointwise comparison.
example (f : List Bool → List Bool) (hf : ∀ xs, ⌜f xs⌝ₜ.size ≤ 3 * ⌜xs⌝ₜ.size) :
    Dominated (fun xs : List Bool => ⌜f xs⌝ₜ.size + 1) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated [hf]

-- An equation in the list rewrites the pointwise goals.
example (f : List Bool → List Bool) (hf : ∀ xs, ⌜f xs⌝ₜ.size = ⌜xs⌝ₜ.size + 1) :
    Dominated (fun xs : List Bool => ⌜f xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated [hf]

-- A strict inequality in the list is used like the others.
example (f : List Bool → List Bool) (hf : ∀ xs, ⌜f xs⌝ₜ.size < ⌜xs⌝ₜ.size + 5) :
    Dominated (fun xs : List Bool => ⌜f xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated [hf]

-- A statement whose left side is an added literal is instantiated at the term it adds to.
example (f : List Bool → List Bool) (hf : ∀ xs, ⌜f xs⌝ₜ.size + 1 = ⌜xs⌝ₜ.size) :
    Dominated (fun xs : List Bool => ⌜f xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated [hf]

-- A statement whose left side is a variable is instantiated at its right side.
example (g : ℕ → List Bool) (hg : ∀ n, n ≤ ⌜g n⌝ₜ.size) :
    Dominated (fun n : ℕ => n) (fun n => ⌜g n⌝ₜ.size) := by
  dominated [hg]

-- A statement whose left side adds a variable is instantiated at the whole sum.
example (f g : ℕ → ℕ) (hf : ∀ x k, f x + k ≤ g x + k) :
    Dominated (fun x => 2 * (f x + 3)) (fun x => g x + 3) := by
  dominated [hf]

-- A `match` under a binder is left to the traversal rules, not split pointwise.
example : Dominated (fun x : Bool × List (Option Bool) => ⌜x.1⌝ₜ.size)
    (fun x => ⌜x⌝ₜ.size + (x.2.map (fun y => match y with | some _ => 1 | none => 0)).sum) := by
  dominated

def twice (xs : List Bool) : List Bool := xs ++ xs

theorem size_encode_twice_le (xs : List Bool) : ⌜twice xs⌝ₜ.size ≤ 2 * ⌜xs⌝ₜ.size := by
  have := size_encode_list_append xs xs
  simp only [twice]
  omega

-- Without the statement, the size of `twice xs` is unknown.
example : Dominated (fun xs : List Bool => ⌜twice xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated
  exact .of_le_mul 2 size_encode_twice_le

attribute [local dominated] size_encode_twice_le in
-- A statement registered with `@[dominated]` is used without being named.
example : Dominated (fun xs : List Bool => ⌜twice xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  dominated

-- A list entry that is neither a definition nor a statement `a ≤ b`, `a < b` or `a = b` is an
-- error.
example : True := by
  fail_if_success
    have : Dominated (fun xs : List Bool => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
      dominated [True.intro]
  trivial

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

-- Guards degrees without coefficients: the base is within a multiple of `p.1.2 + 1` only through
-- the property of the input, and at the exponent 14 a coefficient as large as 8 on the base would
-- exceed the hidden witness `2 ^ 40` if it were carried.
example : Dominated (fun p : {p : ℕ × ℕ // p.1 ≤ 2 * p.2 + 1} => p.1.1 ^ 14)
    (fun p => (p.1.2 + 1) ^ 14) := by
  dominated

-- Guards upper bounds from the property of a subtype input: a variable bounded by a product has the
-- degree of the product.
example : Dominated (fun p : {p : ℕ × ℕ × ℕ // p.1 ≤ p.2.1 * p.2.2} => p.1.1)
    (fun p => (p.1.2.1 + p.1.2.2 + 1) ^ 2) := by
  dominated

-- Guards the same through a conjunction, as subtype properties often are: the factor bounded by
-- `c ^ 2` has degree 2, and the degrees of the factors add up to 3.
example : Dominated (fun p : {p : ℕ × ℕ × ℕ // p.1 ≤ p.2.2 + 1 ∧ p.2.1 ≤ (p.2.2 + 1) ^ 2} =>
    p.1.1 * p.1.2.1) (fun p => (p.1.2.2 + 1) ^ 3) := by
  dominated

/-- A right side whose unfolding has a power. -/
def cubeAbove (x : ℕ) : ℕ := (x + 1) ^ 3 + x

theorem cubeAbove_eq (x : ℕ) : cubeAbove x = (x + 1) ^ 3 + x := rfl

-- Guards reading the right side through the definitions of the list for its powers, without
-- rewriting it.
example : Dominated (fun x : ℕ => x ^ 2) cubeAbove := by
  dominated [cubeAbove]

-- Records a limit of the current design: the right side is read for its powers through the
-- definitions of the list, not through equations about it. When this starts to succeed, the
-- documented limits change.
example : True := by
  fail_if_success
    have : Dominated (fun x : ℕ => x ^ 2) cubeAbove := by
      dominated [cubeAbove_eq]
      done
  trivial

-- Records a limit of the current design: the bases are taken from the right side, not from a power
-- bounding it from below in a hypothesis.
example : True := by
  fail_if_success
    have : Dominated (fun p : {p : ℕ × ℕ // (p.1 + 1) ^ 3 ≤ p.2} => p.1.1 ^ 2)
        (fun p => p.1.2) := by
      dominated
      done
  trivial

-- Guards degree synthesis: the degrees of the factors add, with no coefficient to keep.
example : Dominated (fun x : ℕ × ℕ × ℕ => x.1 * x.2.1 * x.2.2)
    (fun x => (x.1 + x.2.1 + x.2.2 + 1) ^ 3) := by
  dominated

-- Guards products and powers of powers, whose factors are not linear in the base.
example : Dominated (fun x : ℕ => (x + 1) ^ 2 * (x ^ 2) ^ 3) (fun x => (x + 1) ^ 8) := by
  dominated

-- Guards degrees without coefficients: the coefficient `8 ^ 14` would exceed the hidden witness.
example : Dominated (fun x : ℕ => (8 * x + 1) ^ 14) (fun x => (x + 1) ^ 14) := by
  dominated

-- Guards degrees from `Dominated` hypotheses, of any size.
example (f g : ℕ → ℕ) (hf : Dominated f (fun x => (x + 1) ^ 2))
    (hg : Dominated g (fun x => (x + 1) ^ 3)) :
    Dominated (fun x => f x * g x) (fun x => (x + 1) ^ 5) := by
  dominated

-- Guards degrees from statements of the list: `f x` has the degree of its bound `x * x`.
example (f : ℕ → ℕ) (hf : ∀ x, f x ≤ x * x) :
    Dominated (fun x => f x * x) (fun x => (x + 1) ^ 3) := by
  dominated [hf]

-- Guards reading a comparison through linear forms: `p.1 + 1 ≤ p.2 * p.2` bounds `p.1`.
example : Dominated (fun p : {p : ℕ × ℕ // p.1 + 1 ≤ p.2 * p.2} => p.1.1)
    (fun p => (p.1.2 + 1) ^ 2) := by
  dominated

-- Guards bases taken from powers within the terms of the right side.
example : Dominated (fun x : ℕ × ℕ => x.1 * x.1) (fun x => max ((x.1 + 1) ^ 2) x.2) := by
  dominated

-- Guards cases on the condition of an `if`: on its part, the condition bounds the factor.
example : Dominated (fun x : ℕ × ℕ => if x.1 ≤ x.2 then x.1 * x.1 else 0)
    (fun x => (x.2 + 1) ^ 2) := by
  dominated

-- Guards the second pass: the product of the first two factors is bounded as a whole, while each
-- factor alone has degree 1.
example : Dominated (fun p : {p : ℕ × ℕ × ℕ // p.1 * p.2.1 ≤ p.2.2} => p.1.1 * p.1.2.1 * p.1.2.2)
    (fun p => (p.1.1 + p.1.2.1 + p.1.2.2 + 1) ^ 2) := by
  dominated

-- Guards the second pass for a power: `x ^ 2` is bounded as a whole by `y`, while `x` alone, of
-- degree 1/2, counts as degree 1.
example : Dominated (fun p : {p : ℕ × ℕ // p.1 ^ 2 ≤ p.2} => p.1.1 ^ 2 * p.1.2)
    (fun p => (p.1.2 + 1) ^ 2) := by
  dominated

-- Guards the second pass for a difference, whose subtrahend splitting drops.
example : Dominated (fun p : {p : ℕ × ℕ × ℕ // p.1 ≤ p.2.1 + p.2.2} => (p.1.1 - p.1.2.1) ^ 2)
    (fun p => (p.1.2.2 + 1) ^ 2) := by
  dominated

-- Records the provisional treatment of a `match` on a pattern, whose variable `a` degree synthesis
-- cannot see: it is compared pointwise with facts about products and powers.
example : Dominated (fun x : Option (List Bool) × List Bool =>
      match x.1 with | some a => a.length * x.2.length | none => 0)
    (fun x => ⌜x⌝ₜ.size ^ 2) := by
  dominated

-- Records a limit of the current design: one base is used at a time, so a power of a sum of two
-- bases is not compared with the sum of their powers. When this starts to succeed, the documented
-- limits change.
example : True := by
  fail_if_success
    have : Dominated (fun p : ℕ × ℕ => (p.1 + p.2) ^ 2)
        (fun p => (p.1 + 1) ^ 2 + (p.2 + 1) ^ 2) := by
      dominated
      done
  trivial

-- Records a limit of the current design: a product of two bases is not compared with the sum of
-- their squares.
example : True := by
  fail_if_success
    have : Dominated (fun p : ℕ × ℕ => p.1 * p.2) (fun p => (p.1 + 1) ^ 2 + (p.2 + 1) ^ 2) := by
      dominated
      done
  trivial

-- Records a limit of the current design: an atom bounded by a constant still has degree 1.
example : True := by
  fail_if_success
    have : Dominated (fun x : Bool × ℕ => ⌜x.1⌝ₜ.size * x.2 * x.2) (fun x => (x.2 + 1) ^ 2) := by
      dominated
      done
  trivial

-- Records a limit of the current design: splitting keeps only the minuend of a difference that is
-- neither the target nor a fact.
example : True := by
  fail_if_success
    have : Dominated (fun p : {p : ℕ × ℕ × ℕ // p.1 ≤ p.2.1 + p.2.2} => p.1.1 - p.1.2.1)
        (fun p => p.1.2.2 + 1) := by
      dominated
      done
  trivial

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
