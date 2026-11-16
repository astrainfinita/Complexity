/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import ComplexityTest.TreeRun

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

namespace ComplexityTest.SourceTranslation.Traversal

private def mapInput : List (List Bool) := [[true, false], [], [false, true, true]]
private def mapOutput : List (List Bool) := [[false, true], [], [true, true, false]]

-- The program of a certificate is executable model code.
private def mapReverseCode := List.Code.map List.Code.reverse .input
#guard let p := mapReverseCode
  let c := ComplexityTest.TreeRun.runFrom p.compile
    (p.compile.init ⌜mapInput⌝ₜ) 186
  p.compile.halt c.1 && decide (c.2.regs 0 = ⌜mapOutput⌝ₜ)

-- One long callback and many empty callbacks have linear, not quadratic, total time: the time of
-- each callback is linear in its element whatever the state, so the time of the fold is settled
-- without the user. Guards `Dominated.foldlTime_of_size_encode`; if the time comes back as a
-- goal, the rule is no longer applied. The peak holds the states, which the user bounds.
example : HasProgramInO
    (fun x : List Unit × List (List Unit) => x.2.foldl (fun _ ys => ys.reverse) x.1)
    hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  apply Dominated.of_le
  rintro ⟨a, xs⟩
  have := foldlPeak_le_of_size (f := fun _ ys : List Unit => ys.reverse)
    (p := fun z => max ⌜z⌝ₜ.size ⌜z.2⌝ₜ.size) a xs (fun _ _ => by simp [size_encode_prod])
    (fun _ _ => by simp [size_encode_prod])
  simp [size_encode_prod]
  omega

-- Capturing a runtime flag preserves per-element summation: the linear time is settled as well.
private def reverseCaptured (input : Bool × List (List Unit)) : List Unit :=
  input.2.foldl (fun _ ys => if input.1 then ys.reverse else ys) []

example := (by source_fun_prop : HasProgramInO reverseCaptured _ (fun x => ⌜x⌝ₜ.size) _)

section FoldGrowth

-- The growth of a fold is settled without the user: a time polynomial and a peak linear in the
-- code, with a captured value and a bounded accumulator. Guards the fold rules registered with
-- `@[dominated_traversal]`; if this needs a `dominated` line again, they are no longer applied.
example : HasProgramIn (fun x : ℕ × List ℕ => x.2.foldl (fun b u => b || x.1 == u) false)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- The same for nested folds: the inner fold is in the callback of the outer one, and the peak
-- stays linear.
example : HasProgramIn (fun x : List (List ℕ) × ℕ =>
      x.1.foldl (fun b l => b && l.foldl (fun c u => c || x.2 == u) false) true)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private theorem size_foldl_keep_le (n : ℕ) (ys acc : List ℕ) :
    ⌜ys.foldl (fun acc v => if v < n then v :: acc else acc) acc⌝ₜ.size ≤
      ⌜ys⌝ₜ.size + ⌜acc⌝ₜ.size := by
  induction ys generalizing acc with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons]
    by_cases h : y < n
    · have := ih (y :: acc)
      simp only [h, ↓reduceIte, encode_list_cons, size_encode_prod] at this ⊢
      omega
    · have := ih acc
      simp only [h, ↓reduceIte, encode_list_cons, size_encode_prod] at this ⊢
      omega

-- An accumulator that grows needs a bound on the state after every prefix of the list: the user
-- gives it as a lemma about the fold of any list, and the rules do the rest.
example : HasProgramIn
    (fun x : ℕ × List ℕ => x.2.foldl (fun acc v => if v < x.1 then v :: acc else acc) [])
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated [size_foldl_keep_le]

-- A callback known only to be polynomial, given as a hypothesis and applied to a captured value:
-- its growth enters the fold as an opaque function, and the rules still settle the fold. This is
-- the shape of a check of every element of a list by a function taken from a class.
example {α : Type*} [UniqueEncoding Tree α] {V : α × Tree → Bool} {pV : Value → Code Value}
    (hV : HasProgramIn V pV (IsPoly fun t => ⌜t⌝ₜ.size) (IsPoly fun t => ⌜t⌝ₜ.size)) :
    ∃ p, HasProgramIn (fun x : α × List Tree => x.2.foldl (fun b t => b && V (x.1, t)) true) p
      (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) :=
  ⟨_, by source_fun_prop⟩

-- Records a limit: an explicit degree of the time of a fold has no rule of its own. It goes
-- through `Dominated.foldl_of_invariant`, where the user gives the invariant (the remaining list
-- is no larger than the folded one) and the time bound of a round; `dominated` closes the
-- comparisons left, and the linear peak is still settled by the rules. This proof should shrink
-- when explicit time bounds of folds get a rule.
example : HasProgramIn (fun x : ℕ × List ℕ => x.2.foldl (fun b u => b || x.1 == u) false)
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated
  refine (Dominated.foldl_of_invariant (p := fun _ _ => 0)
    (fun (x : ℕ × List ℕ) (rest : List ℕ) (_ : Bool) => ⌜rest⌝ₜ.size ≤ ⌜x.2⌝ₜ.size)
    (fun x => x.2) (fun _ => false) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size)
    (fun _ => le_rfl) (fun _ a rest _ h => (size_encode_tail_le (a :: rest)).trans h)
    ?_ ?_ ?_).1.trans ?_ <;> dominated

end FoldGrowth

section MapGrowth

-- The growth of a map is settled without the user: its time, a sum over the elements, and its
-- result are polynomial in the code. Guards the rules `IsPoly.list_sum` and
-- `IsPoly.size_encode_map` registered with `@[dominated_traversal]`; if this needs a `dominated`
-- line again, they are no longer applied.
example : HasProgramIn (fun xs : List (List ℕ) => xs.map List.reverse) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- The natural linear bounds: the time and the result of each callback are linear in its element,
-- so the time, the result and the peak of the map are linear in the list. Guards
-- `Dominated.list_sum_of_size_encode` and `Dominated.size_encode_map`.
example : HasProgramIn (fun xs : List (List ℕ) => xs.map List.reverse) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- The same with a captured value that leaves the costs of each callback linear in its element.
example : HasProgramIn
    (fun x : Bool × List (List ℕ) => x.2.map (fun l => if x.1 then l.reverse else l))
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Nested maps keep the linear bounds: the inner map is the callback of the outer one.
example : HasProgramIn (fun xs : List (List ℕ) => xs.map (fun l => l.map (· == 0)))
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- A callback whose costs grow with the captured list: the time and the result are the length
-- times the captured list, polynomial but not linear, and the polynomial statement is settled.
example : HasProgramIn (fun x : List ℕ × List (List ℕ) => x.2.map (fun l => x.1 ++ l))
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- A fold in the callback of a map: the fold rules settle each callback, the map rules the sum,
-- and the peak stays linear.
example : HasProgramIn
    (fun x : ℕ × List (List ℕ) => x.2.map (fun l => l.foldl (fun b u => b || u == x.1) false))
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- A map in the callback of a fold, and a fold over a mapped list: the size of the mapped list is
-- the list premise of the fold rules.
example : HasProgramIn
    (fun xs : List (List ℕ) => xs.foldl (fun b l => b && (l.map (· == 0)).isEmpty) true)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn
    (fun xs : List (List ℕ) => (xs.map List.reverse).foldl (fun b l => b && l.isEmpty) true)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Records a limit: a callback known only to be polynomial has no known result size (plan W69),
-- so the user states it, here from the peak of the callback; the map rules do the rest.
example {g : List ℕ → List ℕ} {pg : Value → Code Value}
    (hg : HasProgramIn g pg (IsPoly fun t => ⌜t⌝ₜ.size) (IsPoly fun t => ⌜t⌝ₜ.size)) :
    HasProgramIn (fun xs : List (List ℕ) => xs.map g) hole(pg ⊢ program)
      (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  have : IsPoly (fun y : List ℕ => ⌜y⌝ₜ.size) fun y => ⌜g y⌝ₜ.size :=
    (IsPoly.refl.max hg.isPoly_peak).of_dominated hg.hasProgramInO.size_encode
  fill_hole program in source_fun_prop

-- Records a limit: an explicit degree of the time of a map whose callback costs grow with the
-- captured list has no rule of its own. The user bounds each callback by the input and sums the
-- bound; the linear peak is still settled by the rules. This proof should shrink when explicit
-- time bounds of sums get a rule, as the table sums have (`Dominated.sum_finRange_of_mul`; plan
-- W81).
example : HasProgramIn (fun x : List ℕ × List (List ℕ) => x.2.map (fun l => (x.1 ++ l).isEmpty))
    hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated
  refine (Dominated.list_sum (fun e : List ℕ × List (List ℕ) => e.2) _ (fun e _ => ⌜e⌝ₜ.size)
    (by dominated)).trans ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  dominated

-- Records a limit: the rules are stated for lists of a fixed type, so a map over a list whose
-- element type depends on the input, as a list of indices into a table, keeps its sum and its
-- result to the user. Not settled at all now (plan W82).
example : True := by
  fail_if_success
    have : HasProgramIn (fun x : Σ n, (Fin n → ℕ) × List (Fin n) => x.2.2.map x.2.1)
        hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
      fill_hole program in source_fun_prop
  trivial

end MapGrowth

section AllAnyGrowth

-- A check of every element, or of some element, with a predicate capturing a value is translated
-- without a `via`: it is computed as the conjunction or disjunction of the mapped list, by the
-- view equations `encode_list_all` and `encode_list_any`, so its growth is that of a map and is
-- settled by the same rules: a time polynomial and a peak linear in the code. If these need a
-- `via` or a `dominated` line again, the views are no longer applied.
example : HasProgramIn (fun x : ℕ × List ℕ => x.2.all (fun u => u == x.1)) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn (fun x : ℕ × List ℕ => x.2.any (fun u => u == x.1)) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- A predicate capturing nothing whose costs are linear in its element: the time is linear too.
example : HasProgramIn (fun xs : List ℕ => xs.any (fun u => u == 0)) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Membership is a check of some element with `==` (`encode_list_elem`), for any type whose `==`
-- has an implementation: numbers and Booleans here.
example : HasProgramIn (fun x : ℕ × List ℕ => x.2.contains x.1) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn (fun x : Bool × List Bool => x.2.contains x.1) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Nested checks with membership in a captured list: the shape of evaluating a formula in
-- conjunctive normal form under the assignment that lists the true variables.
example : HasProgramIn
    (fun x : List (List ℕ) × List ℕ => x.1.all (fun l => l.any (fun u => x.2.contains u)))
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private def allOf (p : ℕ → Bool) (xs : List ℕ) : Bool := xs.all p

-- Records a limit: a definition taking a predicate is unfolded only as the source function itself;
-- elsewhere it needs a selected implementation, which a `[program]` statement cannot give, since
-- the predicate has no code.
example : True := by
  fail_if_success
    have : HasProgramIn (fun x : ℕ × List ℕ => allOf (· == x.1) x.2) hole(⊢ program)
        (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
      fill_hole program in source_fun_prop
  trivial

-- The way out: a view equation says how its value is computed. Guards that view equations reach
-- definitions with function arguments.
@[local source_view] private theorem encode_allOf (p : ℕ → Bool) (xs : List ℕ) :
    ⌜allOf p xs⌝ₜ = ⌜xs.all p⌝ₜ := rfl

example : HasProgramIn (fun x : ℕ × List ℕ => allOf (· == x.1) x.2) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

end AllAnyGrowth

section DependentMap

-- A runtime table and its indices share the same runtime length; the table is captured once.
example := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, (Fin n → ℕ) × List (Fin n) => x.2.2.map x.2.1) _ _ _)

-- Pointwise choices must never masquerade as one implementation for all runtime lengths.
example (f : (n : ℕ) → Fin n → Bool) (program : ℕ → Value → Code Value)
    (_hf : ∀ n, HasProgramInO (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgramInO (fun x : Σ n, List (Fin n) => x.2.map (f x.1)) _ _ _)
  trivial

end DependentMap

end ComplexityTest.SourceTranslation.Traversal
