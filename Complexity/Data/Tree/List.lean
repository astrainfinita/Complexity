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

end Complexity.Tree
