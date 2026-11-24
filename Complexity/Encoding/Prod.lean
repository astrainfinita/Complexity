/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic
public import Complexity.Data.Tree.Basic
meta import Mathlib.Util.Notation3

/-! # Basic structured tree codes

Unit and products are the leaves of structural encoding simplification. Their
layouts are explicit lemmas; observations and equality simplify without unfolding them.
-/

@[expose] public section

namespace Complexity

/-- The tree code of a value. -/
scoped notation3 "⌜" x "⌝ₜ" => encode Tree x

/-- The unit of every universe is the empty tree. -/
instance : UniqueEncoding Tree PUnit :=
  UniqueEncoding.ofOption (fun _ ↦ .nil) (fun t ↦ if t = .nil then some .unit else none)
    (by intro a t; cases a; by_cases h : t = .nil <;> simp [h, eq_comm])

instance {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    UniqueEncoding Tree (α × β) :=
  UniqueEncoding.ofDecode (fun p ↦ .pair ⌜p.1⌝ₜ ⌜p.2⌝ₜ)
    (fun (t : Tree) ↦ match t with
      | .nil => Part.none
      | .pair a b => (decode α a).bind fun a ↦ (decode β b).map fun b ↦ (a, b))
    (by rintro ⟨a, b⟩ (_ | ⟨_, l, r⟩) <;>
      simp [Part.mem_bind_iff, Part.mem_map_iff, UniqueEncoding.mem_decode_iff])

/- Lemmas about a unit value are stated for every value, as `PUnit.mul_eq` and `PUnit.max_eq` are:
a lemma rewriting a unit value to `()` would have a variable as its left side and cannot be used
by `simp`. -/

theorem encode_unit (u : PUnit) : ⌜u⌝ₜ = .nil := rfl
theorem encode_prod {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (a : α) (b : β) : ⌜(a, b)⌝ₜ = .pair ⌜a⌝ₜ ⌜b⌝ₜ := rfl

@[simp] theorem root_encode_unit (u : PUnit) : ⌜u⌝ₜ.root = false := rfl
@[simp] theorem left_encode_unit (u : PUnit) : ⌜u⌝ₜ.left = ⌜()⌝ₜ := rfl
@[simp] theorem right_encode_unit (u : PUnit) : ⌜u⌝ₜ.right = ⌜()⌝ₜ := rfl
@[simp] theorem size_encode_unit (u : PUnit) : ⌜u⌝ₜ.size = 1 := rfl
@[simp] theorem eq_encode_unit (u : PUnit) (t : Tree) : t = ⌜u⌝ₜ ↔ t = .nil := Iff.rfl
@[simp] theorem encode_unit_eq (u : PUnit) (t : Tree) : ⌜u⌝ₜ = t ↔ .nil = t := Iff.rfl

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]

@[simp] theorem root_encode_prod (a : α) (b : β) : ⌜(a, b)⌝ₜ.root = true := rfl
@[simp] theorem left_encode_prod (a : α) (b : β) : ⌜(a, b)⌝ₜ.left = ⌜a⌝ₜ := rfl
@[simp] theorem right_encode_prod (a : α) (b : β) :
    ⌜(a, b)⌝ₜ.right = ⌜b⌝ₜ := rfl
@[simp] theorem size_encode_prod (a : α) (b : β) :
    ⌜(a, b)⌝ₜ.size = 1 + ⌜a⌝ₜ.size + ⌜b⌝ₜ.size := rfl

theorem Prod.encode_eq (x : α × β) : ⌜x⌝ₜ = .pair ⌜x.1⌝ₜ ⌜x.2⌝ₜ := rfl

theorem Prod.size_encode_eq (x : α × β) : ⌜x⌝ₜ.size = 1 + ⌜x.1⌝ₜ.size + ⌜x.2⌝ₜ.size := rfl

/-- Each field fits in the encoding of the whole pair, including an opaque pair input. -/
theorem size_encode_fst_le (x : α × β) : ⌜x.1⌝ₜ.size ≤ ⌜x⌝ₜ.size := by
  rcases x with ⟨a, b⟩
  simp only [size_encode_prod]
  omega

theorem size_encode_snd_le (x : α × β) : ⌜x.2⌝ₜ.size ≤ ⌜x⌝ₜ.size := by
  rcases x with ⟨a, b⟩
  simp only [size_encode_prod]
  omega

@[simp] theorem encode_prod_ne_nil (a : α) (b : β) : ⌜(a, b)⌝ₜ ≠ .nil := by
  intro h; cases h
@[simp] theorem nil_ne_encode_prod (a : α) (b : β) : Tree.nil ≠ ⌜(a, b)⌝ₜ :=
  (encode_prod_ne_nil a b).symm

@[simp] theorem pair_eq_encode_prod (l r : Tree) (a : α) (b : β) :
    Tree.pair l r = ⌜(a, b)⌝ₜ ↔ l = ⌜a⌝ₜ ∧ r = ⌜b⌝ₜ := by
  simp only [encode_prod, BinaryTree.node.injEq, true_and]

@[simp] theorem encode_prod_eq_pair (a : α) (b : β) (l r : Tree) :
    ⌜(a, b)⌝ₜ = Tree.pair l r ↔ ⌜a⌝ₜ = l ∧ ⌜b⌝ₜ = r := by
  simp only [encode_prod, BinaryTree.node.injEq, true_and]

/-! The code of a field is a subtree of the structure's code, stated as `T.encode_field`;
`@[tree_encoding]` states it for the structures it derives. -/

theorem _root_.Prod.encode_fst (x : α × β) : ⌜x.1⌝ₜ = ⌜x⌝ₜ.subtree [false] := rfl

theorem _root_.Prod.encode_snd (x : α × β) : ⌜x.2⌝ₜ = ⌜x⌝ₜ.subtree [true] := rfl

theorem _root_.Subtype.encode_val {p : α → Prop} (x : {a // p a}) :
    ⌜x.1⌝ₜ = ⌜x⌝ₜ.subtree [] := rfl

end Complexity
