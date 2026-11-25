/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Primitives

/-! # Reading bit strings as trees by tree programs

`BitList.hasProgramIn_toTree`: `BitList.toTree`, which reads every bit string as a tree, takes time
and peak linear in the code of the string. The guess of `nstack_of_tree_verifier` is read by it.
-/

@[expose] public section

namespace Complexity

open TreeProgram TreeProgram.Source

theorem BitList.hasProgramIn_toTreeStep :
    HasProgramIn (fun x : List Tree × Bool => toTreeStep x.1 x.2) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programToTreeStep
  fill_hole program in source_fun_prop

attribute [local program] BitList.hasProgramIn_toTreeStep in
/-- Reading a bit string as a tree takes time and peak linear in its code. -/
@[program] theorem BitList.hasProgramIn_toTree : HasProgramIn toTree hole(⊢ program)
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programToTree
  -- The stacks after the prefixes of the reversed string, for the fold, and at its end.
  have hstack (xs ys : List Bool) (h : ys.length ≤ xs.length) :
      ⌜ys.foldl toTreeStep []⌝ₜ.size ≤ 3 * ⌜xs⌝ₜ.size := by
    have hy := size_encode_foldl_toTreeStep_le ys []
    have := length_le_codeSize xs
    have := Tree.size_pos ⌜xs⌝ₜ
    simp only [encode_list_nil, size_encode_unit] at hy
    omega
  have hacc : Dominated (fun z : {z : List Bool × List Bool // z.2 <+: z.1.reverse} =>
      ⌜z.1.2.foldl toTreeStep []⌝ₜ.size) fun z => ⌜z.1.1⌝ₜ.size :=
    Dominated.of_le_mul 3 fun z => hstack _ _ (z.2.length_le.trans_eq (List.length_reverse ..))
  have hres : Dominated (fun xs : List Bool => ⌜xs.reverse.foldl toTreeStep []⌝ₜ.size)
      fun xs => ⌜xs⌝ₜ.size :=
    Dominated.of_le_mul 3 fun xs => hstack _ _ (List.length_reverse ..).le
  -- The top of the stack, by a program of its own with a `match` on its input: `List.headD` has no
  -- selected implementation (plan W91), and a `match` on the result of the fold leaves its peak
  -- open (plan W87). This is the current workaround, not a decision.
  have hhead : HasProgramIn (fun stack : List Tree => stack.headD .nil) hole(⊢ head)
      IsO(fun _ => 1) IsO(fun stack => ⌜stack⌝ₜ.size) := by
    fill_hole head in source_fun_prop via
      (fun stack : List Tree => match stack with | t :: _ => t | [] => .nil)
    case source_eq => funext stack; cases stack <;> rfl
  fill_hole program in source_fun_prop

end Complexity
