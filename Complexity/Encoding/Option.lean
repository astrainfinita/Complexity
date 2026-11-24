/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Prod
public import Complexity.Data.Tree.Basic

/-! # Compact tree encodings of optional values -/

@[expose] public section

namespace Complexity

/-- A missing value is a leaf; a present value occupies the right child of a node. -/
def Tree.encodeOption {α : Type*} (f : α → Tree) : Option α → Tree
  | none => .nil
  | some a => .pair .nil (f a)

/-- Reject nonempty left children, preserving a unique representation. -/
def Tree.decodeOption {α : Type*} (f : Tree → Part α) : Tree → Part (Option α)
  | .nil => pure none
  | .pair .nil t => some <$> f t
  | _ => Part.none

theorem Tree.mem_decodeOption_iff {α : Type*} [UniqueEncoding Tree α]
    (t : Tree) (a : Option α) :
    a ∈ Tree.decodeOption (decode α) t ↔ Tree.encodeOption (encode Tree) a = t := by
  cases t with
  | nil => cases a <;> simp [Tree.decodeOption, Tree.encodeOption]
  | node label l r =>
    cases label
    cases l <;> cases a <;> simp [Tree.decodeOption, Tree.encodeOption,
      Part.mem_map_iff, UniqueEncoding.mem_decode_iff]

instance {α : Type*} [UniqueEncoding Tree α] : UniqueEncoding Tree (Option α) :=
  UniqueEncoding.ofDecode (Tree.encodeOption (encode Tree)) (Tree.decodeOption (decode α))
    fun a t ↦ Tree.mem_decodeOption_iff t a

@[simp] theorem encode_option_none {α : Type*} [UniqueEncoding Tree α] :
    ⌜(none : Option α)⌝ₜ = ⌜()⌝ₜ := rfl

@[simp] theorem encode_option_some {α : Type*} [UniqueEncoding Tree α] (a : α) :
    ⌜some a⌝ₜ = ⌜((), a)⌝ₜ := rfl

/-- The code of a present value has two more nodes than the value's code. -/
theorem size_encode_option_some {α : Type*} [UniqueEncoding Tree α] (a : α) :
    ⌜some a⌝ₜ.size = ⌜a⌝ₜ.size + 2 := by
  rw [encode_option_some, size_encode_prod, size_encode_unit]
  omega

end Complexity
