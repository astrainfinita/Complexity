/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree.Encoding

/-! # Internal prefix codes for tree-machine data -/

@[expose] public section

namespace Complexity.TreeMachine

/-- Internal tape representation of a tree. -/
def code (a : Tree) : List (Option Bool) := (BitList.encodeTree a).map some

@[simp] theorem code_nil : code Tree.nil = [some false] := rfl

@[simp] theorem code_pair (a b : Tree) :
    code (Tree.pair a b) = some true :: (code a ++ code b) := by
  simp [code]

@[simp] theorem length_code (a : Tree) : (code a).length = a.size := by simp [code]

end Complexity.TreeMachine
