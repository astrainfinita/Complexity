/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree.Basic

/-! # Lists represented by right-associated trees -/

@[expose] public section

namespace Complexity.Tree

/-- Encode elements along the left children and the remaining list along the right children. -/
def encodeList {α : Type*} (f : α → Tree) : List α → Tree
  | [] => nil
  | a :: as => pair (f a) (encodeList f as)

@[simp] theorem encodeList_nil {α : Type*} (f : α → Tree) : encodeList f [] = nil := rfl

@[simp] theorem encodeList_cons {α : Type*} (f : α → Tree) (a : α) (as : List α) :
    encodeList f (a :: as) = pair (f a) (encodeList f as) := rfl

/-- Length of the right spine, viewing a tree as a list of its left children. -/
@[simp] def listLength : Tree → ℕ
  | nil => 0
  | pair _ xs => xs.listLength + 1

/-- Reverse the right spine onto a given tail, preserving the element trees. -/
@[simp] def reverseAppend : Tree → Tree → Tree
  | nil, ys => ys
  | pair x xs, ys => xs.reverseAppend (pair x ys)

@[simp] theorem listLength_encodeList {α : Type*} (f : α → Tree) (xs : List α) :
    (encodeList f xs).listLength = xs.length := by
  induction xs <;> simp_all

@[simp] theorem listLength_reverseAppend (xs ys : Tree) :
    (xs.reverseAppend ys).listLength = xs.listLength + ys.listLength := by
  induction xs generalizing ys with
  | nil => simp
  | node u x xs ihx ih =>
    cases u
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (pair x ys)

/-- Reversal moves nodes between the cursor and accumulator without increasing total size. -/
theorem size_reverseAppend (xs ys : Tree) :
    (xs.reverseAppend ys).size + 1 = xs.size + ys.size := by
  induction xs generalizing ys with
  | nil => simp [Nat.add_comm]
  | node u x xs ihx ih =>
    cases u
    have h := ih (pair x ys)
    simp only [reverseAppend, size_pair] at *
    omega

@[simp] theorem reverseAppend_encodeList {α : Type*} (f : α → Tree) (xs ys : List α) :
    (encodeList f xs).reverseAppend (encodeList f ys) = encodeList f (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simpa only [encodeList_cons, reverseAppend, List.reverse_cons, List.append_assoc,
      List.singleton_append] using ih (x :: ys)

/-- The left children along the right spine of a tree; its code is the tree itself. -/
def spine : Tree → List Tree
  | .nil => []
  | .node _ a b => a :: spine b

/-- A tree is a node exactly when its spine list is nonempty. -/
theorem root_eq_not_isEmpty_spine (t : Tree) : t.root = !t.spine.isEmpty := by
  cases t <;> rfl

end Complexity.Tree
