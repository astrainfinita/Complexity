/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree.Encoding

/-! # Lists of bits represented by trees -/

@[expose] public section

namespace Complexity.Tree

/-- A Boolean occupies a leaf or a pair of leaves. -/
def encodeBool : Bool → Tree
  | false => nil
  | true => pair nil nil

/-- A list is a right-associated chain of pairs, terminated by a leaf. -/
def encodeBitList : List Bool → Tree
  | [] => nil
  | b :: bs => pair (encodeBool b) (encodeBitList bs)

@[simp] theorem encodeBool_false : encodeBool false = nil := rfl
@[simp] theorem encodeBool_true : encodeBool true = pair nil nil := rfl
@[simp] theorem encodeBitList_nil : encodeBitList [] = nil := rfl
@[simp] theorem encodeBitList_cons (b : Bool) (bs : List Bool) :
    encodeBitList (b :: bs) = pair (encodeBool b) (encodeBitList bs) := rfl

theorem size_encodeBool_le (b : Bool) : (encodeBool b).size ≤ 3 := by cases b <;> decide

theorem size_encodeBitList_le (bs : List Bool) : (encodeBitList bs).size ≤ 4 * bs.length + 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have := size_encodeBool_le b
    simp only [encodeBitList_cons, size_pair, List.length_cons]
    omega

theorem length_le_size_encodeBitList (bs : List Bool) : bs.length ≤ (encodeBitList bs).size := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp only [encodeBitList_cons, size_pair, List.length_cons]; omega

theorem encodeBool_injective : Function.Injective encodeBool := by
  intro a b h
  cases a <;> cases b <;> simp_all

theorem encodeBitList_injective : Function.Injective encodeBitList := by
  intro as bs h
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [encodeBitList_cons, BinaryTree.node.injEq, true_and] at h
      exact congrArg₂ List.cons (encodeBool_injective h.1) (ih h.2)

end Complexity.Tree
