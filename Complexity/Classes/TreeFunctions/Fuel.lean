/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Primitives
public import Complexity.Classes.TreeFunctions.Composition

/-! # Polynomial-time fuel

`exists_fuel_mem_fp`: for a bound polynomial in the input code size, a polynomial-time function
gives a list of units at least as long. It turns a polynomial bound into fuel computed by a tree
machine, as `nstack_of_bits_verifier` takes it.

The list is the code size in unary (`Fuel.countNodes`, a recursion on a worklist of trees), with its
length squared a fixed number of times (`Fuel.square`).
-/

@[expose] public section

namespace Complexity.TreeMachine.Fuel

open TreeProgram TreeProgram.Source

/-- One step on a worklist of trees: drop a leaf, or replace a node by its two subtrees. -/
def expand : List Tree → List Tree
  | [] => []
  | t :: rest => match t with
    | .nil => rest
    | .pair a b => a :: b :: rest

/-- The total size of the trees of a worklist. -/
def work (ws : List Tree) : ℕ := (ws.map Tree.size).sum

/-- One unit for every node and leaf of the worklist, and one more. -/
def countNodes : List Tree → List Unit
  | [] => [()]
  | .nil :: rest => () :: countNodes rest
  | .pair a b :: rest => () :: countNodes (a :: b :: rest)
termination_by ws => work ws
decreasing_by all_goals simp [work] <;> omega

theorem length_countNodes (ws : List Tree) : (countNodes ws).length = work ws + 1 := by
  induction ws using countNodes.induct <;> simp_all [countNodes, work] <;> omega

/-- `countNodes` as a recursion with one call per branch. -/
def countRecursion : Recursion countNodes where
  test ws := !ws.isEmpty
  next := expand
  finish _ := [()]
  resume _ r := () :: r
  finish_eq := by
    rintro ⟨_ | _, h⟩
    · simp [countNodes]
    · simp at h
  resume_eq := by
    rintro ⟨_ | ⟨_ | ⟨⟨⟩, a, b⟩, rest⟩, h⟩
    · simp at h
    · simp [countNodes, expand]
    · simp [countNodes, expand]
  measure := work
  decreases := by
    rintro (_ | ⟨_ | ⟨⟨⟩, a, b⟩, rest⟩) h
    · simp at h
    · simp [expand, work]
    · simp [expand, work]; omega

theorem work_le_size (ws : List Tree) : work ws ≤ ⌜ws⌝ₜ.size := by
  rw [size_encode_list]
  exact Nat.le_succ_of_le (Nat.le_add_right _ _)

/-- A step keeps the code of the worklist from growing: the scale of the recursion. -/
theorem size_expand_le (ws : List Tree) : ⌜expand ws⌝ₜ.size ≤ ⌜ws⌝ₜ.size := by
  rcases ws with _ | ⟨_ | ⟨⟨⟩, a, b⟩, rest⟩
  · simp [expand]
  · simp [expand, encode_list_cons, size_encode_prod]
  · simp [expand, encode_list_cons, size_encode_prod]; omega

theorem hasProgramIn_countTest : HasProgramIn (fun ws : List Tree => !ws.isEmpty)
    hole(⊢ program) IsO(fun _ => 1) IsO(fun ws => ⌜ws⌝ₜ.size) := by
  abstract_hole program using programCountTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_expand : HasProgramIn expand hole(⊢ program) IsO(fun _ => 1)
    IsO(fun ws => ⌜ws⌝ₜ.size) := by
  abstract_hole program using programExpand
  fill_hole program in source_fun_prop

theorem hasProgramIn_countFinish : HasProgramIn countRecursion.finish hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCountFinish
  fill_hole program in source_fun_prop

theorem hasProgramIn_countResume :
    HasProgramIn (fun x : countRecursion.Return => countRecursion.resume x.1 x.2)
      hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCountResume
  fill_hole program in source_fun_prop

theorem hasProgramIn_countNodes : HasProgramIn countNodes hole(⊢ program)
    (IsPoly fun ws => ⌜ws⌝ₜ.size) (IsPoly fun ws => ⌜ws⌝ₜ.size) := by
  abstract_hole program using programCountNodes
  fill_hole program in
    exact countRecursion.hasProgramIn_isPoly (fun ws => ⌜ws⌝ₜ.size)
      (fun ws _ => size_expand_le ws) (IsPoly.refl.of_dominated (Dominated.of_le work_le_size))
      .refl
      ⟨1, 5, fun ws => by
        have := work_le_size ws
        simp only [size_encode_list_unit, length_countNodes, pow_one, smul_eq_mul]
        omega⟩
      hasProgramIn_countTest.isPoly (.const 1) .refl
      hasProgramIn_expand.isPoly (.const 1) .refl
      hasProgramIn_countFinish.isPoly (.const 1) .refl
      hasProgramIn_countResume.isPoly (.const 1) .refl

attribute [local program] hasProgramIn_countNodes in
/-- The unary code size of any uniquely encoded value. -/
theorem countNodes_encode_mem_fp {α : Type*} [UniqueEncoding Tree α] :
    (fun a : α => countNodes [⌜a⌝ₜ]) ∈ FP .sizeCostTree := by
  model_fun_prop

/-- A list whose length is the square of the length of `l`. -/
def square (l : List Unit) : List Unit := l.foldl (fun acc _ => acc ++ l) []

theorem length_square (l : List Unit) : (square l).length = l.length ^ 2 := by
  simp [square, sq]

theorem hasProgramIn_square : HasProgramIn square hole(⊢ program)
    (IsPoly fun l => ⌜l⌝ₜ.size) (IsPoly fun l => ⌜l⌝ₜ.size) := by
  abstract_hole program using programSquare
  -- The accumulator after each prefix of the list, which the fold rules ask for.
  have hacc : IsPoly (fun z : {z : List Unit × List Unit // z.2 <+: z.1} => ⌜z.1.1⌝ₜ.size)
      fun z => ⌜z.1.2.foldl (fun acc _ => acc ++ z.1.1) []⌝ₜ.size := by
    refine ⟨2, 1, fun z => ?_⟩
    have h1 : (z.1.2.foldl (fun acc _ => acc ++ z.1.1) []).length =
        z.1.2.length * z.1.1.length := by simp
    have h2 := z.2.length_le
    simp only [size_encode_list_unit, h1, smul_eq_mul, Nat.one_mul]
    nlinarith
  fill_hole program in source_fun_prop

theorem iterate_square_mem_fp (k : ℕ) : square^[k] ∈ FP .sizeCostTree := by
  induction k with
  | zero => exact fp_id
  | succ k ih =>
    rw [Function.iterate_succ']
    exact fp_comp hasProgramIn_square.mem_fp_sizeCost ih

theorem length_iterate_square (k : ℕ) (l : List Unit) :
    (square^[k] l).length = l.length ^ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', length_square, ih, ← pow_mul, pow_succ]

end Complexity.TreeMachine.Fuel

namespace Complexity.TreeMachine

open Fuel

/-- A bound polynomial in the input code size is exceeded by the length of a list of units computed
in polynomial time. -/
theorem exists_fuel_mem_fp {α : Type*} [UniqueEncoding Tree α] (b : α → ℕ)
    (hb : IsPoly (fun a => ⌜a⌝ₜ.size) b) :
    ∃ fuel : α → List Unit, fuel ∈ FP .sizeCostTree ∧ ∀ a, b a ≤ (fuel a).length := by
  obtain ⟨d, C, h⟩ := hb
  refine ⟨fun a => square^[C + d] (countNodes [⌜a⌝ₜ]), ?_, fun a => ?_⟩
  · exact fp_comp (iterate_square_mem_fp _) countNodes_encode_mem_fp
  · have hn : 2 ≤ ⌜a⌝ₜ.size + 1 := Nat.succ_le_succ (Tree.size_pos _)
    rw [length_iterate_square, length_countNodes]
    simp only [work, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    calc b a ≤ C * (⌜a⌝ₜ.size + 1) ^ d := by simpa using h a
      _ ≤ (⌜a⌝ₜ.size + 1) ^ C * (⌜a⌝ₜ.size + 1) ^ d :=
        Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hn C))
      _ = (⌜a⌝ₜ.size + 1) ^ (C + d) := (pow_add _ _ _).symm
      _ ≤ (⌜a⌝ₜ.size + 1) ^ 2 ^ (C + d) := Nat.pow_le_pow_right (by omega) Nat.lt_two_pow_self.le

end Complexity.TreeMachine
