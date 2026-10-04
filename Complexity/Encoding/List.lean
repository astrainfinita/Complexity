/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic
public import Complexity.Data.Tree.List

/-! # Tree encodings of lists -/

@[expose] public section

namespace Complexity

/-- Interpret each left child as an element and the right spine as the remaining list. -/
def Tree.decodeList {α : Type*} (f : Tree → Part α) : Tree → Part (List α)
  | .nil => pure []
  | .pair a b => do
      let a ← f a
      let b ← Tree.decodeList f b
      pure (a :: b)

theorem Tree.mem_decodeList_iff {α : Type*} [UniqueEncoding Tree α] (t : Tree) (as : List α) :
    as ∈ Tree.decodeList (decode α) t ↔ Tree.encodeList (encode Tree) as = t := by
  induction t generalizing as with
  | nil => cases as <;> simp [Tree.decodeList]
  | node label a b ha hb =>
    cases label
    cases as <;> simp [Tree.decodeList, Part.mem_bind_iff, Part.mem_some_iff,
      UniqueEncoding.mem_decode_iff, hb]

instance {α : Type*} [UniqueEncoding Tree α] : UniqueEncoding Tree (List α) :=
  UniqueEncoding.ofDecode (Tree.encodeList (encode Tree)) (Tree.decodeList (decode α))
    fun as t ↦ Tree.mem_decodeList_iff t as

@[simp] theorem encode_list_nil {α : Type*} [UniqueEncoding Tree α] :
    encode Tree ([] : List α) = .nil := rfl

@[simp] theorem encode_list_cons {α : Type*} [UniqueEncoding Tree α] (a : α) (as : List α) :
    encode Tree (a :: as) = .pair (encode Tree a) (encode Tree as) := rfl

end Complexity
