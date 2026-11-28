/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.List.OfFn
public import Complexity.Encoding.List
public import Complexity.Tactic.Dominated.Attr

/-! # Fixed-length vectors given by their entries, and their encodings

`FinVector α n` is a vector of `n` entries; it means the same as Lean core's `Vector α n`.
Programs store fixed-length tables, such as the wire tables of circuits, as `FinVector`s.

## Representation

In Lean today, `Vector` cannot easily reconcile a definition that suits proofs, the
type-theoretic indexing function `Fin n → α`, with a convenient compiled representation, an
`Array` together with a proof of its size. The library is written for proofs rather than for
running Lean code, so `FinVector` is defined directly as a structure wrapping `Fin n → α`, which
makes it a type of its own.

How a machine model stores a vector is a separate question, answered by its encoding. The tree
encoding is currently the list of entries, whose length is supplied by the type: indexing entry
`i` follows the spine path `List.replicate i true ++ [false]` and takes `O(i)` steps, and the
encoding lemmas below state this list layout. A layout with `O(log i)` access can replace it
without changing this type. The encoding depends only on the encoding of lists, not on an
encoding `UniqueEncoding Tree (Fin n → α)`.

## The source-translation boundary

Wrapping the indexing function keeps `Fin`-functions out of translated programs: a program reads,
maps, extends and passes `FinVector`s, and only uses `v.get` at the boundary of an operation that
takes a function. Three invariants preserve this boundary.

* `FinVector.ofFn` has no `simp` encoding equation and no translation rule, so a program cannot
  build a vector from an arbitrary function. For the same reason `encode_finVector` is not
  `@[simp]`: the translation looks up constructor encodings in the default `simp` set, and would
  otherwise match `⌜FinVector.ofFn f⌝ₜ`.
* `FinVector` is not derived with `@[tree_encoding]`, so the translation has no field equation
  `FinVector.encode_get` that would compute `v.get` as the stored `v`.
* `⌜v.get⌝ₜ = ⌜v⌝ₜ` is not a `source_view`, so `v.get` is not computed as `v` either.
-/

@[expose] public section

namespace Complexity

universe u

/-! ### Vectors and their operations -/

/-- A vector of `n` entries, given by its indexing function. -/
@[ext] structure FinVector (α : Type u) (n : ℕ) where
  /-- The vector with the given entries. -/
  ofFn ::
  /-- The entry at an index. -/
  get : Fin n → α

namespace FinVector

variable {α β : Type*} {m n : ℕ}

/-- The entries in increasing index order. -/
def toList (v : FinVector α n) : List α := List.ofFn v.get

/-- Apply a function to every entry. -/
def map (f : α → β) (v : FinVector α n) : FinVector β n := ofFn (f ∘ v.get)

/-- Add an entry after the last one. -/
def push (v : FinVector α n) (a : α) : FinVector α (n + 1) := ofFn (Fin.snoc v.get a)

/-- The entries of `v` followed by those of `w`. -/
def append (v : FinVector α m) (w : FinVector α n) : FinVector α (m + n) :=
  ofFn (Fin.append v.get w.get)

instance : HAppend (FinVector α m) (FinVector α n) (FinVector α (m + n)) := ⟨append⟩

/-- The vector of all indices, in increasing order. -/
def finRange (n : ℕ) : FinVector (Fin n) n := ofFn id

@[simp] theorem ofFn_get (v : FinVector α n) : ofFn v.get = v := rfl

@[simp] theorem get_ofFn (f : Fin n → α) : (ofFn f).get = f := rfl

theorem get_map (f : α → β) (v : FinVector α n) : (v.map f).get = f ∘ v.get := rfl

theorem get_push (v : FinVector α n) (a : α) : (v.push a).get = Fin.snoc v.get a := rfl

theorem get_append (v : FinVector α m) (w : FinVector α n) :
    (v ++ w).get = Fin.append v.get w.get := rfl

theorem get_finRange (n : ℕ) : (finRange n).get = id := rfl

@[simp] theorem toList_ofFn (f : Fin n → α) : (ofFn f).toList = List.ofFn f := rfl

@[simp] theorem length_toList (v : FinVector α n) : v.toList.length = n := List.length_ofFn

theorem toList_injective : Function.Injective (toList (α := α) (n := n)) :=
  fun _ _ h => FinVector.ext (List.ofFn_injective h)

/-- Decided by comparing the lists of entries. -/
instance [DecidableEq α] : DecidableEq (FinVector α n) := fun v w =>
  decidable_of_iff (v.toList = w.toList) ⟨fun h => toList_injective h, congrArg toList⟩

@[simp] theorem getElem_toList (v : FinVector α n) (i : ℕ) (h : i < v.toList.length) :
    v.toList[i] = v.get ⟨i, by simpa using h⟩ :=
  List.getElem_ofFn ..

@[simp] theorem mem_toList_iff (v : FinVector α n) (a : α) : a ∈ v.toList ↔ ∃ i, v.get i = a :=
  List.mem_ofFn

@[simp] theorem toList_map (f : α → β) (v : FinVector α n) :
    (v.map f).toList = v.toList.map f :=
  (List.map_ofFn (f := v.get) (g := f)).symm

@[simp] theorem toList_push (v : FinVector α n) (a : α) :
    (v.push a).toList = v.toList ++ [a] := by
  rw [toList, push, get_ofFn, List.ofFn_succ']
  simp [toList]

@[simp] theorem toList_append (v : FinVector α m) (w : FinVector α n) :
    (v ++ w).toList = v.toList ++ w.toList :=
  List.ofFn_fin_append v.get w.get

/-- Looking the list of a vector up at an index of the vector finds the entry. -/
theorem getElem?_toList_val (v : FinVector α n) (i : Fin n) :
    v.toList[i.val]? = some (v.get i) := by
  simp [toList]

end FinVector

/-! ### Encoding

A vector uses the list encoding of its entries. -/

/-- Recover a vector from a list of the required length. -/
def List.decodeFinVector {α : Type*} (n : ℕ) (xs : List α) : Option (FinVector α n) :=
  if h : xs.length = n then some (.ofFn fun i => xs.get (Fin.cast h.symm i)) else none

theorem List.decodeFinVector_eq_some_iff {α : Type*} {n : ℕ} (xs : List α) (v : FinVector α n) :
    List.decodeFinVector n xs = some v ↔ v.toList = xs := by
  unfold List.decodeFinVector
  split
  · rename_i h
    subst n
    rw [Option.some.injEq, ← FinVector.toList_injective.eq_iff, eq_comm]
    simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact h (by simp)

/-- A vector uses the list of its entries. -/
instance {R α : Type*} [c : UniqueEncoding R (List α)] {n : ℕ} :
    UniqueEncoding R (FinVector α n) :=
  c.ofLeftInjection FinVector.toList (fun xs => Part.ofOption (List.decodeFinVector n xs))
    fun xs v => by
      simpa only [Part.mem_coe, Option.mem_def] using List.decodeFinVector_eq_some_iff xs v

theorem encode_finVector {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ} (v : FinVector α n) :
    encode R v = encode R v.toList := rfl

@[dominated] theorem size_encode_finVector_toList {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) : ⌜v.toList⌝ₜ.size = ⌜v⌝ₜ.size :=
  rfl

/-- The code of an entry of a vector is a subtree of the vector's code, at a path fixed by its
index. -/
theorem encode_finVector_get_apply {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) (i : Fin n) :
    ⌜v.get i⌝ₜ = ⌜v⌝ₜ.subtree (List.replicate i.val true ++ [false]) := by
  rw [encode_finVector, ← encode_list_getElem v.toList i.val (by simp), FinVector.getElem_toList]

/-- Pointwise representation changes preserve the representation of a vector. -/
theorem encode_finVector_map_of_encode {α β : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] {n : ℕ} (f : α → β) (h : ∀ x, ⌜f x⌝ₜ = ⌜x⌝ₜ) (v : FinVector α n) :
    ⌜v.map f⌝ₜ = ⌜v⌝ₜ := by
  rw [encode_finVector, encode_finVector, FinVector.toList_map, encode_list_map_of_encode f h]

/-- A vector's code has at least as many nodes as its length. -/
@[dominated] theorem card_le_size_encode_finVector {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) : n ≤ ⌜v⌝ₜ.size := by
  rw [encode_finVector, size_encode_list, FinVector.length_toList]
  omega

/-- An entry of a vector is part of the vector's code. -/
@[dominated] theorem size_encode_finVector_get_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) (i : Fin n) : ⌜v.get i⌝ₜ.size ≤ ⌜v⌝ₜ.size :=
  size_encode_le_list_of_mem ((FinVector.mem_toList_iff v _).mpr ⟨i, rfl⟩)

/-- A vector's code fits within its length times a uniform entry-code bound plus spine overhead. -/
theorem size_encode_finVector_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ} (v : FinVector α n)
    (bound : ℕ) (h : ∀ i, ⌜v.get i⌝ₜ.size ≤ bound) : ⌜v⌝ₜ.size ≤ n * (bound + 1) + 1 := by
  simpa only [encode_finVector, FinVector.length_toList] using size_encode_list_le v.toList bound
    (by simpa only [FinVector.mem_toList_iff, forall_exists_index, forall_apply_eq_imp_iff]
      using h)

/-- Pushing an entry stores it and one more list node. -/
@[dominated] theorem size_encode_finVector_push {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) (a : α) : ⌜v.push a⌝ₜ.size = ⌜v⌝ₜ.size + ⌜a⌝ₜ.size + 1 := by
  have h := size_encode_list_append v.toList [a]
  simp only [encode_list_cons, encode_list_nil, size_encode_prod, size_encode_unit] at h
  simp only [encode_finVector, FinVector.toList_push]
  omega

/-- Concatenated vectors store the entries of both, as the concatenated lists do. -/
@[dominated] theorem size_encode_finVector_append {α : Type*} [UniqueEncoding Tree α] {m n : ℕ}
    (v : FinVector α m) (w : FinVector α n) : ⌜v ++ w⌝ₜ.size + 1 = ⌜v⌝ₜ.size + ⌜w⌝ₜ.size := by
  simpa only [encode_finVector, FinVector.toList_append] using
    size_encode_list_append v.toList w.toList

end Complexity
