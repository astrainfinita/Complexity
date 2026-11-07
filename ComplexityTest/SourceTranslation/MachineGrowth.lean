/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgram)
namespace ComplexityTest.SourceTranslation.MachineGrowth

-- The time budget depends on the value, without imposing a size envelope.
theorem identity_machine : TimeSpaceModel.tree.ComputableIn
    (id : List Bool → List Bool) IsO(fun xs => xs.length + 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop

-- A local implementation is used by the machine exit.
example {program : Value → Code Value}
    (_hf : HasProgram (id : List Bool → List Bool) program (fun _ => 0) (fun _ => 0)) :
    TimeSpaceModel.tree.ComputableIn (id : List Bool → List Bool)
      IsO(fun _ => 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop

-- Loading and running still cost time: a zero machine allowance cannot replace the program.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableIn (id : List Bool → List Bool)
        IsO(fun _ => 0) IsO(fun xs => ⌜xs⌝ₜ.size) := by
      model_fun_prop
      all_goals exact Dominated.zero
  trivial

-- The all-input machine budget does not become vacuous on finite input types.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableIn (id : Unit → Unit)
        IsO(fun _ => 0) IsO(fun _ => 0) := by
      model_fun_prop
      all_goals exact Dominated.zero
  trivial

/-- A deliberately slower program for the identity, saved as the selected implementation. -/
@[program] theorem hasProgramIn_selected :
    HasProgramIn (id : List Bool → List Bool) hole(⊢ program) IsO(fun xs => ⌜xs⌝ₜ.size)
    IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programSelected
  refine HasProgram.toHasProgramIn ?_
  fill_hole program in
    exact ((List.hasProgramIn_reverse.toHasProgram.comp
      List.hasProgramIn_reverse.toHasProgram).congr (by funext xs; simp)).mono
      (Dominated.of_le_mul 2 fun _ => by simp; omega) (Dominated.of_le fun _ => by simp)

-- Direct exits keep the stated growth of the selected implementation.
theorem canonical_machine : TimeSpaceModel.tree.ComputableIn
    (id : List Bool → List Bool) IsO(fun xs => ⌜xs⌝ₜ.size + 4)
      IsO(fun xs => max ⌜xs⌝ₜ.size ⌜xs⌝ₜ.size + 2) :=
  hasProgramIn_selected.computableIn

example := (by source_fun_prop : HasProgram (id : List Bool → List Bool) programSelected _ _)

-- Guards the polynomial exit: `model_fun_prop` proves the time growth polynomial in the input
-- code size by `dominated`, and no degree is written.
theorem reverse_fp : (List.reverse : List Bool → List Bool) ∈ FP .tree := by
  model_fun_prop

-- Guards `dominated` on `IsPoly` goals: sums, products, powers and constants by their closure
-- rules, the other parts compared linearly with the input code size.
example : IsPoly (fun x : List Bool × List Bool => ⌜x⌝ₜ.size)
    (fun x => ⌜x.1⌝ₜ.size * ⌜x.2⌝ₜ.size + (x.1.length + 1) ^ 3 + 7) := by
  dominated

-- Guards upper bounds on `IsPoly` goals: a part bounded by a product in a listed statement is
-- polynomial by the closure rules applied to the bound.
example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ n * n) : IsPoly id f := by
  dominated [hf]

-- Guards composition on `IsPoly` goals: a function polynomial by a hypothesis, applied to a part
-- whose code size is polynomial in the input code size.
example (T : List Bool → ℕ) (hT : IsPoly (fun y => ⌜y⌝ₜ.size) T) :
    IsPoly (fun x : List Bool × List Bool => ⌜x⌝ₜ.size) fun x => T x.1 * T x.2 + 1 := by
  dominated

-- Guards traversals on `IsPoly` goals: a maximum over a list element by element, the elements
-- polynomial uniformly in the measure of their input.
example : IsPoly (fun x : ℕ × List ℕ => ⌜x⌝ₜ.size)
    (fun x => x.2.foldr (fun y s => max (⌜x⌝ₜ.size * ⌜y⌝ₜ.size) s) 0) := by
  dominated

-- Guards table sums on `IsPoly` goals: the length and each entry polynomial.
example : IsPoly (fun n : ℕ => n)
    (fun n => ((List.finRange n).map fun i : Fin n => (i : ℕ) * (i : ℕ)).sum) := by
  dominated

-- Guards cases on the condition of an `if` on `IsPoly` goals: on its part, the condition bounds
-- the factor.
example : IsPoly (fun x : ℕ × ℕ => x.2) (fun x => if x.1 ≤ x.2 then x.1 * x.1 else 0) := by
  dominated

-- Guards a difference compared as a whole on `IsPoly` goals when its minuend is not polynomial:
-- only the difference is bounded, by the property of the subtype.
example : IsPoly (fun p : {p : ℕ × ℕ × ℕ // p.1 ≤ p.2.1 + p.2.2} => p.1.2.2)
    (fun p => (p.1.1 - p.1.2.1) ^ 2) := by
  dominated

-- Guards that on `IsPoly` goals, as on `Dominated` goals, the parts not proved are left as goals:
-- here the factor `f n`, whose bound is not given to `dominated`.
example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ n ^ 3) : IsPoly (fun n : ℕ => n) fun n => n * f n + 1 := by
  dominated
  exact IsPoly.of_dominated (IsPoly.refl.pow 3) (Dominated.of_le hf)

-- Records a limit of the current design: on `IsPoly` goals a `match` on a pattern is compared
-- pointwise only, so a product of its pattern variables is not proved (plan W2). When this starts
-- to succeed, the documented limits change.
example : True := by
  fail_if_success
    have : IsPoly (fun x : Option (List Bool) × List Bool => ⌜x⌝ₜ.size)
        (fun x => match x.1 with | some a => a.length * x.2.length | none => 0) := by
      dominated
      done
  trivial

-- Guards that a growth that is not polynomial in the code size is not proved: numbers are
-- encoded in binary, so `x + 1` is exponential in the code size of `x`.
example : True := by
  fail_if_success
    have : IsPoly (fun x : ℕ => ⌜x⌝ₜ.size) fun x => x + 1 := by dominated
  trivial

end ComplexityTest.SourceTranslation.MachineGrowth
