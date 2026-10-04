/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.BitList
public import Complexity.Data.Tree.BitList

/-! # Boolean encodings

A Boolean result is represented by a singleton bit string, or by the existing
leaf/pair tree representation. Both interpretations reject all other codes.
-/

@[expose] public section

namespace Complexity

namespace BitList

/-- Encode a Boolean as a singleton bit string. -/
def encodeBool (b : Bool) : List Bool := [b]

/-- Decode a Boolean from a singleton bit string, rejecting all other strings. -/
def decodeBool : List Bool → Option Bool
  | [b] => some b
  | _ => none

theorem decodeBool_eq_some_iff {xs : List Bool} {b : Bool} :
    decodeBool xs = some b ↔ encodeBool b = xs := by
  cases xs with
  | nil => simp [decodeBool, encodeBool]
  | cons a xs => cases xs <;> simp [decodeBool, encodeBool, eq_comm]

@[simp] theorem decodeBool_encodeBool (b : Bool) : decodeBool (encodeBool b) = some b :=
  decodeBool_eq_some_iff.mpr rfl

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

end Tree

/-- A Boolean occupies exactly one bit. -/
instance : UniqueEncoding (List Bool) Bool :=
  UniqueEncoding.ofOption BitList.encodeBool BitList.decodeBool fun _ _ =>
    BitList.decodeBool_eq_some_iff

/-- A Boolean occupies a leaf or a pair of leaves. -/
instance : UniqueEncoding Tree Bool :=
  UniqueEncoding.ofOption Tree.encodeBool Tree.decodeBool fun _ _ => Tree.decodeBool_eq_some_iff

@[simp] theorem encode_bool_bits (b : Bool) : encode (List Bool) b = [b] := rfl

@[simp] theorem encode_bool_tree (b : Bool) : encode Tree b = Tree.encodeBool b := rfl

@[simp] theorem mem_decode_bool_bits {b : Bool} {xs : List Bool} :
    b ∈ decode Bool xs ↔ xs = [b] :=
  UniqueEncoding.mem_decode_iff.trans eq_comm

@[simp] theorem mem_decode_bool_tree {b : Bool} {a : Tree} :
    b ∈ decode Bool a ↔ Tree.encodeBool b = a :=
  UniqueEncoding.mem_decode_iff

end Complexity
