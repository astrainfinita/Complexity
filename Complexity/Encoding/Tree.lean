/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.BitList
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

/-- Read a list tree as a bit string; reject trees outside the image of `encodeBitList`. -/
def decodeBitList : Tree → Option (List Bool)
  | nil => some []
  | pair a b => do
      let x ← decodeBool a
      let xs ← decodeBitList b
      pure (x :: xs)

theorem decodeBitList_eq_some_iff {a : Tree} {xs : List Bool} :
    decodeBitList a = some xs ↔ encodeBitList xs = a := by
  induction a generalizing xs with
  | nil => cases xs <;> simp [decodeBitList]
  | node v a b ha hb =>
      cases v
      cases xs <;> simp [decodeBitList, Option.bind_eq_some_iff, decodeBool_eq_some_iff, hb]

@[simp] theorem decodeBitList_encodeBitList (xs : List Bool) :
    decodeBitList (encodeBitList xs) = some xs :=
  decodeBitList_eq_some_iff.mpr rfl

end Tree

/-- The existing prefix code, with exactly one complete tree per string. -/
instance : UniqueEncoding (List Bool) Tree :=
  UniqueEncoding.ofOption BitList.encodeTree BitList.decodeTree fun _ _ ↦
    BitList.decodeTree_eq_some_iff

/-- The existing right-associated list tree encoding of bit strings. -/
instance bitListEncoding : UniqueEncoding Tree (List Bool) :=
  UniqueEncoding.ofOption Tree.encodeBitList Tree.decodeBitList fun _ _ ↦
    Tree.decodeBitList_eq_some_iff

end Complexity
