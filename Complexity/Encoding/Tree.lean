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
the whole string; `BitList.toTree` reads every bit string as a tree, a prefix code as its tree.
The encoding boundary is provided by `Encoding.RawWord`.
-/

@[expose] public section

namespace Complexity

/-- Raw trees use the identity encoding. -/
instance : UniqueEncoding Tree Tree := UniqueEncoding.refl Tree

@[simp] theorem Tree.encode_self (a : Tree) : ⌜a⌝ₜ = a := rfl

/-- The code of a code is the code itself. -/
theorem Tree.encode_encode {α : Type*} [UniqueEncoding Tree α] (a : α) : ⌜⌜a⌝ₜ⌝ₜ = ⌜a⌝ₜ := rfl

@[simp] theorem Tree.decode_self (a : Tree) : decode Tree a = Part.some a := rfl

/-- The code of the spine list is the tree itself. -/
theorem Tree.encode_spine (t : Tree) : ⌜t.spine⌝ₜ = ⌜t⌝ₜ := by
  induction t with
  | nil => rfl
  | node u a b _ hb => cases u; simp only [Tree.spine, encode_list_cons, encode_prod]; simp_all

@[dominated] theorem Tree.size_encode_spine (t : Tree) : ⌜t.spine⌝ₜ.size = ⌜t⌝ₜ.size := by
  rw [Tree.encode_spine]

/-- The spine of the code of a list is the list of the codes of its elements. -/
theorem Tree.spine_encode_list {α : Type*} [UniqueEncoding Tree α] (l : List α) :
    ⌜l⌝ₜ.spine = l.map (encode Tree) :=
  UniqueEncoding.encode_injective <|
    (Tree.encode_spine _).trans (encode_list_map_of_encode _ Tree.encode_encode l).symm

/-- A tree is the code of a list exactly when every tree of its spine is the code of an element. -/
theorem exists_encode_list_eq_iff {α : Type*} [UniqueEncoding Tree α] {t : Tree} :
    (∃ l : List α, ⌜l⌝ₜ = t) ↔ ∀ e ∈ t.spine, ∃ a : α, ⌜a⌝ₜ = e := by
  refine ⟨fun ⟨l, hl⟩ e he => ?_, fun h => ?_⟩
  · rw [← hl, Tree.spine_encode_list, List.mem_map] at he
    obtain ⟨a, -, rfl⟩ := he
    exact ⟨a, rfl⟩
  · suffices ∀ s : List Tree, (∀ e ∈ s, ∃ a : α, ⌜a⌝ₜ = e) → ∃ l : List α, ⌜l⌝ₜ = ⌜s⌝ₜ from
      (this _ h).imp fun _ hl => hl.trans (Tree.encode_spine t)
    intro s hs
    induction s with
    | nil => exact ⟨[], rfl⟩
    | cons e s ih =>
      obtain ⟨a, rfl⟩ := hs e List.mem_cons_self
      obtain ⟨l, hl⟩ := ih fun e he => hs e (List.mem_cons_of_mem _ he)
      exact ⟨a :: l, by simp only [encode_list_cons, encode_prod, hl, Tree.encode_self]⟩

/-- A node is computed as the pair of its subtrees. -/
theorem Tree.encode_pair (a b : Tree) : ⌜Tree.pair a b⌝ₜ = ⌜(a, b)⌝ₜ := rfl

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

/-- One step of reading a prefix code from its end: a leaf is pushed onto the stack, and a node
joins the two trees on top, the first one on the left. -/
def toTreeStep (stack : List Tree) (b : Bool) : List Tree :=
  match b with
  | false => .nil :: stack
  | true => match stack with
    | a :: c :: rest => .pair a c :: rest
    | stack => stack

/-- Read a bit string as the prefix code of a tree, on every bit string: the string is read from
its end with a stack of trees, and the tree on top is the result, or a leaf. A prefix code gives its
tree (`toTree_encodeTree`). -/
def toTree (xs : List Bool) : Tree :=
  (xs.reverse.foldl toTreeStep []).headD .nil

theorem foldl_toTreeStep_reverse_encodeTree (a : Tree) (stack : List Tree) :
    (encodeTree a).reverse.foldl toTreeStep stack = a :: stack := by
  induction a generalizing stack with
  | nil => rfl
  | node u a b ha hb =>
    cases u
    simp [List.foldl_append, ha, hb, toTreeStep]

@[simp] theorem toTree_encodeTree (a : Tree) : toTree (encodeTree a) = a := by
  rw [toTree, foldl_toTreeStep_reverse_encodeTree]
  rfl

/-- Each step adds at most two nodes to the code of the stack. -/
theorem size_encode_foldl_toTreeStep_le (xs : List Bool) (stack : List Tree) :
    ⌜xs.foldl toTreeStep stack⌝ₜ.size ≤ ⌜stack⌝ₜ.size + 2 * xs.length := by
  induction xs generalizing stack with
  | nil => simp
  | cons b xs ih =>
    have : ⌜toTreeStep stack b⌝ₜ.size ≤ ⌜stack⌝ₜ.size + 2 := by
      rcases b with _ | _
      · simp only [toTreeStep, encode_list_cons, size_encode_prod, Tree.encode_self, Tree.size_nil]
        omega
      · rcases stack with _ | ⟨a, _ | ⟨c, rest⟩⟩ <;>
          simp only [toTreeStep, encode_list_cons, size_encode_prod, Tree.encode_self,
            Tree.size_pair] <;> omega
    have := ih (toTreeStep stack b)
    simp only [List.foldl_cons, List.length_cons]
    omega

@[dominated] theorem size_toTree_le (xs : List Bool) : (toTree xs).size ≤ 2 * xs.length + 1 := by
  have h := size_encode_foldl_toTreeStep_le xs.reverse []
  simp only [encode_list_nil, size_encode_unit, List.length_reverse] at h
  rw [toTree]
  rcases hs : xs.reverse.foldl toTreeStep [] with _ | ⟨t, rest⟩
  · simp
  · rw [hs, encode_list_cons, size_encode_prod, Tree.encode_self] at h
    rw [List.headD_cons]
    omega

end BitList

end Complexity
