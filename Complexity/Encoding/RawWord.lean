/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Complexity.Encoding.Composition
public import Complexity.Data.RawWord
meta import Mathlib.Util.Notation3

/-! # Raw words and serialized tree encodings

Tree encodings induce raw Boolean-word encodings. Raw words themselves have only
the identity encoding; use their underlying lists to encode them as structured data.
-/

@[expose] public section

namespace Complexity

namespace RawWord

instance {Γ : Type*} : UniqueEncoding (RawWord Γ) (RawWord Γ) := UniqueEncoding.refl _

@[simp] theorem encode_self {Γ : Type*} (w : RawWord Γ) : encode (RawWord Γ) w = w := rfl
@[simp] theorem decode_self {Γ : Type*} (w : RawWord Γ) : decode (RawWord Γ) w = Part.some w := rfl

/-- One complete prefix code, rejecting any unconsumed suffix. -/
@[instance_reducible, simps! -isSimp encode]
def treeEncoding : UniqueEncoding (RawWord Bool) Tree :=
  UniqueEncoding.ofOption (fun t ↦ ofList (BitList.encodeTree t))
    (fun w ↦ BitList.decodeTree w.toList) fun t w ↦ by
      rw [BitList.decodeTree_eq_some_iff, ← toList_inj]

@[simp] theorem length_treeEncoding (t : Tree) :
    (treeEncoding.encode t).length = t.size := BitList.length_encodeTree t

end RawWord

/-- Any tree interpretation induces an interpretation of serialized Boolean words. -/
instance (priority := low) {α : Type*} [e : Encoding Tree α] : Encoding (RawWord Bool) α :=
  RawWord.treeEncoding.toEncoding.comp e

/-- Serialize after forming the tree code, including for subtypes and finite indices. -/
instance (priority := 1100) {α : Type*} [e : UniqueEncoding Tree α] :
    UniqueEncoding (RawWord Bool) α := RawWord.treeEncoding.comp e

/-- The serialized tree code of a value, as a raw Boolean word. -/
scoped notation3 "⌜" x "⌝₂" => encode (RawWord Bool) x

theorem encode_rawWord {α : Type*} [UniqueEncoding Tree α] (a : α) :
    ⌜a⌝₂ = RawWord.ofList (BitList.encodeTree ⌜a⌝ₜ) := rfl

theorem length_encode_rawWord {α : Type*} [UniqueEncoding Tree α] (a : α) :
    ⌜a⌝₂.length = ⌜a⌝ₜ.size :=
  RawWord.length_treeEncoding _

end Complexity
