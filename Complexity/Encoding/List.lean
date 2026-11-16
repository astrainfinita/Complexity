/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Prod
public import Complexity.Data.Tree.List
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Complexity.Tactic.Dominated.Attr

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

@[simp, dominated_simp] theorem encode_list_nil {α : Type*} [UniqueEncoding Tree α] :
    ⌜([] : List α)⌝ₜ = ⌜()⌝ₜ := rfl

@[simp, dominated_simp]
theorem encode_list_cons {α : Type*} [UniqueEncoding Tree α] (a : α) (as : List α) :
    ⌜a :: as⌝ₜ = ⌜(a, as)⌝ₜ := rfl

/-- Pointwise representation changes preserve the representation of a list. -/
theorem encode_list_map_of_encode {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] (f : α → β)
    (h : ∀ x, ⌜f x⌝ₜ = ⌜x⌝ₜ) (xs : List α) : ⌜xs.map f⌝ₜ = ⌜xs⌝ₜ := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [encode_prod, h, ih]

/-- A list stores its elements together with one node per cons and a final leaf. -/
theorem size_encode_list {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    ⌜xs⌝ₜ.size = (xs.map fun x => ⌜x⌝ₜ.size).sum + xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [encode_list_cons, size_encode_prod, List.map_cons,
      List.sum_cons, List.length_cons, ih]; omega

theorem size_encode_list_le {α : Type*} [UniqueEncoding Tree α] (xs : List α)
    (bound : ℕ) (h : ∀ x ∈ xs, ⌜x⌝ₜ.size ≤ bound) :
    ⌜xs⌝ₜ.size ≤ xs.length * (bound + 1) + 1 := by
  have hs := List.sum_le_sum h
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul] at hs
  rw [size_encode_list]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- Concatenation replaces the first list's final leaf with the second list. -/
@[dominated] theorem size_encode_list_append {α : Type*} [UniqueEncoding Tree α] (xs ys : List α) :
    ⌜xs ++ ys⌝ₜ.size + 1 = ⌜xs⌝ₜ.size + ⌜ys⌝ₜ.size := by
  simp only [size_encode_list, List.map_append, List.sum_append, List.length_append]
  omega

@[dominated] theorem size_encode_tail_le {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    ⌜xs.tail⌝ₜ.size ≤ ⌜xs⌝ₜ.size := by
  cases xs <;> simp [size_encode_prod]

/-- A sublist keeps a subset of the element codes and of the list nodes. -/
theorem _root_.List.Sublist.size_encode_le {α : Type*} [UniqueEncoding Tree α] {xs ys : List α}
    (h : xs.Sublist ys) : ⌜xs⌝ₜ.size ≤ ⌜ys⌝ₜ.size := by
  have hs := (h.map fun x => ⌜x⌝ₜ.size).sum_le_sum fun _ _ => Nat.zero_le _
  have hl := h.length_le
  simp only [size_encode_list]
  omega

/-- A prefix is a sublist. -/
@[dominated_forward] theorem _root_.List.IsPrefix.size_encode_le {α : Type*}
    [UniqueEncoding Tree α] {xs ys : List α} (h : xs <+: ys) : ⌜xs⌝ₜ.size ≤ ⌜ys⌝ₜ.size :=
  h.sublist.size_encode_le

@[dominated_forward] theorem size_encode_le_list_of_mem {α : Type*} [UniqueEncoding Tree α]
    {x : α} {xs : List α} (hx : x ∈ xs) : ⌜x⌝ₜ.size ≤ ⌜xs⌝ₜ.size := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩ :
    ⌜x⌝ₜ.size ∈ xs.map (fun a => ⌜a⌝ₜ.size))
  rw [size_encode_list]
  omega

@[simp] theorem listLength_encode_unit : ⌜()⌝ₜ.listLength = 0 := rfl

@[simp] theorem listLength_encode_prod {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] (a : α) (b : β) :
    ⌜(a, b)⌝ₜ.listLength = ⌜b⌝ₜ.listLength + 1 := rfl

@[simp↓] theorem listLength_encode_list {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    ⌜xs⌝ₜ.listLength = xs.length := Tree.listLength_encodeList _ _

@[simp↓] theorem reverseAppend_encode_list {α : Type*} [UniqueEncoding Tree α]
    (xs ys : List α) :
    ⌜xs⌝ₜ.reverseAppend ⌜ys⌝ₜ = ⌜xs.reverse ++ ys⌝ₜ :=
  Tree.reverseAppend_encodeList _ _ _

end Complexity
