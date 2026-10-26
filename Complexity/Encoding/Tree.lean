/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Bool
public import Complexity.Encoding.List
public import Complexity.Data.Tree.Encoding

/-! # Tree and bit string encodings

The complete tree parser accepts the existing prefix code only when it consumes
the whole string. The encoding boundary is provided by `Encoding.RawWord`.
-/

@[expose] public section

namespace Complexity

/-- Raw trees use the identity encoding. -/
instance : UniqueEncoding Tree Tree := UniqueEncoding.refl Tree

@[simp] theorem Tree.encode_self (a : Tree) : ⌜a⌝ₜ = a := rfl

/-- The code of a code is the code itself. -/
theorem Tree.encode_encode {α : Type*} [UniqueEncoding Tree α] (a : α) : ⌜⌜a⌝ₜ⌝ₜ = ⌜a⌝ₜ := rfl

@[simp] theorem Tree.decode_self (a : Tree) : decode Tree a = Part.some a := rfl

namespace BitList

/-- Parse one tree and reject any unconsumed suffix. -/
def decodeTree (xs : List Bool) : Option Tree :=
  (parseTree xs).bind fun p ↦ if p.2 = [] then some p.1 else none

theorem decodeTree_eq_some_iff {xs : List Bool} {a : Tree} :
    decodeTree xs = some a ↔ encodeTree a = xs := by
  simpa [decodeTree, Option.bind_eq_some_iff, Prod.exists, parseTree_eq_some_iff] using
    (eq_comm : xs = encodeTree a ↔ encodeTree a = xs)

@[simp] theorem decodeTree_encodeTree (a : Tree) : decodeTree (encodeTree a) = some a :=
  decodeTree_eq_some_iff.mpr rfl

end BitList

end Complexity
