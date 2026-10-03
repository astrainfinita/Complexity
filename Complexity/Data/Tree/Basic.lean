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

/-- The only observation available to a tree machine's finite control. -/
def root : Tree → Bool
  | nil => false
  | pair _ _ => true

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
  cases a <;> simp only [BinaryTree.left, size] <;> omega

theorem size_right_le (a : Tree) : size a.right ≤ size a := by
  cases a <;> simp only [BinaryTree.right, size] <;> omega

end Tree

end Complexity
