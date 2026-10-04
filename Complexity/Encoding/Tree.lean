/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Bool
public import Complexity.Encoding.List
public import Complexity.Data.Tree.BitList

/-! # Tree and bit string encodings

The existing tree prefix code is accepted only when it consumes the whole string.
In the other direction, a bit string is represented by its existing list tree.
-/

@[expose] public section

namespace Complexity

/-- Raw trees use the identity encoding. -/
instance : UniqueEncoding Tree Tree := UniqueEncoding.refl Tree

@[simp] theorem Tree.encode_self (a : Tree) : encode Tree a = a := rfl

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

/-- The existing prefix code, with exactly one complete tree per string. -/
instance : UniqueEncoding (List Bool) Tree :=
  UniqueEncoding.ofOption BitList.encodeTree BitList.decodeTree fun _ _ ↦
    BitList.decodeTree_eq_some_iff

/-- The existing right-associated list tree encoding of bit strings. -/
@[instance_reducible]
def bitListEncoding : UniqueEncoding Tree (List Bool) := inferInstance

end Complexity
