/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Prod
public import Complexity.Data.Tree.BitList

/-! # Boolean encodings

Booleans keep the existing leaf/pair tree representation. Raw bit encodings
are obtained by serializing the tree, just as for other structured values.
-/

@[expose] public section

namespace Complexity

namespace Tree

/-- Read a leaf or a pair of leaves as a Boolean; reject other trees. -/
def decodeBool : Tree → Option Bool
  | nil => some false
  | pair nil nil => some true
  | _ => none

theorem decodeBool_eq_some_iff {a : Tree} {b : Bool} :
    decodeBool a = some b ↔ encodeBool b = a := by
  cases b <;> cases a with
  | nil => simp [decodeBool]
  | node v a c =>
      cases v
      cases a <;> cases c <;> simp [decodeBool]

end Tree

/-- A Boolean occupies a leaf or a pair of leaves. -/
instance : UniqueEncoding Tree Bool :=
  UniqueEncoding.ofOption Tree.encodeBool Tree.decodeBool fun _ _ => Tree.decodeBool_eq_some_iff

theorem encode_bool_tree (b : Bool) : ⌜b⌝ₜ = Tree.encodeBool b := rfl

@[simp] theorem encode_bool_false : ⌜false⌝ₜ = ⌜()⌝ₜ := rfl
@[simp] theorem encode_bool_true : ⌜true⌝ₜ = ⌜((), ())⌝ₜ := rfl

@[simp] theorem root_encode_bool (b : Bool) : ⌜b⌝ₜ.root = b := by
  cases b <;> rfl

@[simp] theorem size_encode_bool (b : Bool) : ⌜b⌝ₜ.size = if b then 3 else 1 := by
  cases b <;> rfl

theorem size_encode_bool_le (b : Bool) : ⌜b⌝ₜ.size ≤ 3 := by
  cases b <;> simp

end Complexity
