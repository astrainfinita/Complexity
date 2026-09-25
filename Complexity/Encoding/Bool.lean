/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree

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

/-- A Boolean occupies exactly one bit. -/
instance boolBitListEncoding : UniqueEncoding (List Bool) Bool :=
  UniqueEncoding.ofOption BitList.encodeBool BitList.decodeBool fun _ _ =>
    BitList.decodeBool_eq_some_iff

/-- A Boolean occupies a leaf or a pair of leaves. -/
instance boolTreeEncoding : UniqueEncoding Tree Bool :=
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
