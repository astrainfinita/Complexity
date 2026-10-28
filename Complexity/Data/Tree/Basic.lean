/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Data.List.Basic

/-!
# Unlabelled binary trees

We use mathlib's `BinaryTree Unit`. `size` counts both internal nodes and leaves,
so even `nil` has size one. Trees have value semantics, independently of runtime sharing.
-/

@[expose] public section

namespace Complexity

/-- Unlabelled binary trees, with `nil` as the default value. -/
abbrev Tree := BinaryTree Unit

namespace Tree

/-- The empty tree. -/
@[match_pattern] abbrev nil : Tree := BinaryTree.nil

/-- A binary node with no label. -/
@[match_pattern] abbrev pair (a b : Tree) : Tree := BinaryTree.node () a b

/-- The left subtree, or a leaf. Simplification preserves projections of unknown trees. -/
def left : Tree → Tree := BinaryTree.left

/-- The right subtree, or a leaf. -/
def right : Tree → Tree := BinaryTree.right

@[simp] theorem left_nil : left nil = nil := rfl
@[simp] theorem left_pair (a b : Tree) : left (pair a b) = a := rfl
@[simp] theorem right_nil : right nil = nil := rfl
@[simp] theorem right_pair (a b : Tree) : right (pair a b) = b := rfl

/-- The only observation available to a tree machine's finite control. -/
def root : Tree → Bool
  | nil => false
  | pair _ _ => true

/-- The subtree at a path of `false` (left) and `true` (right) steps. -/
def subtree (t : Tree) : List Bool → Tree
  | [] => t
  | r :: path => (if r then t.right else t.left).subtree path

theorem subtree_append (t : Tree) (p q : List Bool) :
    t.subtree (p ++ q) = (t.subtree p).subtree q := by
  induction p generalizing t with
  | nil => rfl
  | cons r p ih => exact ih _

@[simp] theorem root_nil : root nil = false := rfl

@[simp] theorem root_pair (a b : Tree) : root (pair a b) = true := rfl

@[simp] theorem root_eq_false {a : Tree} : root a = false ↔ a = nil := by
  cases a <;> simp [root]

/-- The number of nodes, including leaves, in the fully expanded tree. -/
def size : Tree → ℕ
  | nil => 1
  | pair a b => 1 + size a + size b

@[simp] theorem size_nil : size nil = 1 := rfl

@[simp] theorem size_pair (a b : Tree) : size (pair a b) = 1 + size a + size b := rfl

theorem size_pos (a : Tree) : 0 < size a := by
  cases a <;> simp only [size] <;> omega

theorem size_left_le (a : Tree) : size a.left ≤ size a := by
  cases a <;> simp only [left, BinaryTree.left, size] <;> omega

theorem size_right_le (a : Tree) : size a.right ≤ size a := by
  cases a <;> simp only [right, BinaryTree.right, size] <;> omega

theorem size_subtree_le (a : Tree) (path : List Bool) : size (a.subtree path) ≤ size a := by
  induction path generalizing a with
  | nil => exact Nat.le_refl _
  | cons r path ih =>
    refine Nat.le_trans (ih _) ?_
    cases r
    · exact size_left_le a
    · exact size_right_le a

end Tree

end Complexity
