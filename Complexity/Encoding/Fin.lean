/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Vector
public import Complexity.Encoding.FinVector
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Complexity.Tactic.Dominated.Attr

/-! # Encodings of bounded indices and finite tuples -/

@[expose] public section

namespace Complexity

/-- A bounded index uses its natural-number code. -/
instance {R : Type*} [c : UniqueEncoding R ℕ] {n : ℕ} : UniqueEncoding R (Fin n) :=
  (c.subtype (· < n)).ofEquiv Fin.equivSubtype

@[simp high, dominated_expand]
theorem encode_fin {R : Type*} [UniqueEncoding R ℕ] {n : ℕ} (i : Fin n) :
    encode R i = encode R i.val := rfl

theorem _root_.Fin.encode_val [UniqueEncoding Tree ℕ] {n : ℕ} (i : Fin n) :
    ⌜i.val⌝ₜ = ⌜i⌝ₜ.subtree [] := rfl

/-- Recover a finite tuple from a list of the required length. -/
def List.decodeFinFunction {α : Type*} (n : ℕ) (xs : List α) : Option (Fin n → α) :=
  if h : xs.length = n then some (fun i => xs.get (Fin.cast h.symm i)) else none

theorem List.decodeFinFunction_eq_some_iff {α : Type*} {n : ℕ}
    (xs : List α) (f : Fin n → α) :
    List.decodeFinFunction n xs = some f ↔ List.ofFn f = xs := by
  unfold List.decodeFinFunction
  split
  · rename_i h
    subst n
    simp only [Fin.cast_refl, id_eq, Option.some.injEq]
    constructor
    · rintro rfl
      exact List.ofFn_get xs
    · intro h
      apply List.ofFn_injective
      rw [List.ofFn_get, h]
  · rename_i h
    constructor
    · intro h'
      cases h'
    · intro h'
      exact (h (by rw [← h', List.length_ofFn])).elim

/-- A finite tuple uses the list of its values in increasing index order. -/
instance {R α : Type*} [c : UniqueEncoding R (List α)] {n : ℕ} :
    UniqueEncoding R (Fin n → α) :=
  c.ofLeftInjection List.ofFn (fun xs => Part.ofOption (List.decodeFinFunction n xs))
    fun xs f => by
      simpa only [Part.mem_coe, Option.mem_def] using List.decodeFinFunction_eq_some_iff xs f

@[simp] theorem encode_fin_function {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ}
    (f : Fin n → α) : encode R f = encode R (List.ofFn f) := rfl

@[dominated] theorem size_encode_ofFn {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) : ⌜List.ofFn f⌝ₜ.size = ⌜f⌝ₜ.size := rfl

theorem encode_ofFn {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ} (f : Fin n → α) :
    encode R (List.ofFn f) = encode R f := rfl

/-- A finite tuple has the code of its vector of values. -/
theorem encode_fin_function_vector {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ}
    (f : Fin n → α) : encode R f = encode R (Vector.ofFn f) := by
  rw [encode_fin_function, encode_vector, Vector.toList_ofFn]

theorem encode_vector_ofFn {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ} (f : Fin n → α) :
    encode R (Vector.ofFn f) = encode R f :=
  (encode_fin_function_vector f).symm

@[dominated] theorem size_encode_vector_ofFn {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) : ⌜Vector.ofFn f⌝ₜ.size = ⌜f⌝ₜ.size := by
  rw [encode_vector_ofFn]

/-- Appending a tuple entry uses the ordinary list representation. -/
@[simp high] theorem encode_fin_snoc {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (a : α) : ⌜Fin.snoc f a⌝ₜ = ⌜List.ofFn f ++ [a]⌝ₜ := by
  rw [encode_fin_function, List.ofFn_succ']
  simp

/-- Concatenated tuples store the entries of both, as the concatenated lists do. -/
@[dominated] theorem size_encode_fin_append {α : Type*} [UniqueEncoding Tree α] {n m : ℕ}
    (f : Fin n → α) (g : Fin m → α) : ⌜Fin.append f g⌝ₜ.size + 1 = ⌜f⌝ₜ.size + ⌜g⌝ₜ.size := by
  simpa only [encode_fin_function, List.ofFn_fin_append] using
    size_encode_list_append (List.ofFn f) (List.ofFn g)

/-- Erasing bounds from a tuple of wire indices does not change its representation. -/
@[simp high] theorem encode_fin_values [UniqueEncoding Tree ℕ] {n k : ℕ}
    (f : Fin k → Fin n) : ⌜List.ofFn (Fin.val ∘ f)⌝ₜ = ⌜List.ofFn f⌝ₜ := by
  simp only [← List.map_ofFn]
  exact encode_list_map_of_encode Fin.val (fun _ => rfl) _

@[simp] theorem encode_finRange [UniqueEncoding Tree ℕ] (n : ℕ) :
    ⌜List.finRange n⌝ₜ = ⌜List.range n⌝ₜ := by
  rw [← List.map_coe_finRange_eq_range, ← List.ofFn_id]
  simpa only [List.map_ofFn] using (encode_fin_values (id : Fin n → Fin n)).symm

/-- The vector of all indices is stored as the list of the numbers below its length. -/
theorem encode_finVector_finRange [UniqueEncoding Tree ℕ] (n : ℕ) :
    ⌜FinVector.finRange n⌝ₜ = ⌜List.range n⌝ₜ := by
  rw [encode_finVector, ← encode_finRange]
  rfl

/-- Increasing the bound on stored indices does not traverse or change their codes. -/
@[simp high, dominated_expand] theorem encode_finVector_map_castSucc [UniqueEncoding Tree ℕ]
    {n k : ℕ} (v : FinVector (Fin k) n) : ⌜v.map Fin.castSucc⌝ₜ = ⌜v⌝ₜ :=
  encode_finVector_map_of_encode Fin.castSucc (fun _ => rfl) v

/-- Erasing the bounds of stored indices does not traverse or change their codes. -/
@[simp high, dominated_expand] theorem encode_finVector_map_val [UniqueEncoding Tree ℕ] {n k : ℕ}
    (v : FinVector (Fin k) n) : ⌜v.map Fin.val⌝ₜ = ⌜v⌝ₜ :=
  encode_finVector_map_of_encode Fin.val (fun _ => rfl) v

/-- An index stored in a vector, as a number, fits in the vector; `encode_fin` expands the index's
code to that of the number. -/
@[dominated] theorem size_encode_val_finVector_get_le [UniqueEncoding Tree ℕ] {n m : ℕ}
    (v : FinVector (Fin m) n) (i : Fin n) : ⌜(v.get i).val⌝ₜ.size ≤ ⌜v⌝ₜ.size :=
  size_encode_finVector_get_le v i

/-- An index stored in a vector given by its entries, as a number, fits in the vector. Case
analysis that exposes a vector as `FinVector.ofFn f` reduces its entries to `f i`, which
`size_encode_val_finVector_get_le` no longer matches. -/
@[dominated] theorem size_encode_val_apply_le_finVector_ofFn [UniqueEncoding Tree ℕ] {n m : ℕ}
    (f : Fin n → Fin m) (i : Fin n) : ⌜(f i).val⌝ₜ.size ≤ ⌜FinVector.ofFn f⌝ₜ.size :=
  size_encode_finVector_get_le (FinVector.ofFn f) i

/-- A vector read through another vector at its entries stores one entry of the other vector for
each of its own entries. -/
@[dominated] theorem size_encode_finVector_map_get_le {α : Type*} [UniqueEncoding Tree ℕ]
    [UniqueEncoding Tree α] {n k : ℕ} (w : FinVector α k) (v : FinVector (Fin k) n) :
    ⌜v.map w.get⌝ₜ.size ≤ ⌜v⌝ₜ.size * (⌜w⌝ₜ.size + 1) + 1 :=
  (size_encode_finVector_le _ ⌜w⌝ₜ.size fun i => size_encode_finVector_get_le w (v.get i)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (card_le_size_encode_finVector v)) 1)

/-- A represented tuple is also the list of its element codes, without a traversal. -/
theorem encode_fin_function_codes {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) : ⌜List.ofFn (fun i => ⌜f i⌝ₜ)⌝ₜ = ⌜f⌝ₜ := by
  rw [encode_fin_function]
  simpa only [List.map_ofFn, Function.comp_def] using
    encode_list_map_of_encode (encode Tree) (fun _ : α => Tree.encode_self _) (List.ofFn f)

/-- Pointwise equal element codes give the same stored finite table. -/
theorem encode_fin_function_congr {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {n : ℕ}
    (f : Fin n → α) (g : Fin n → β) (h : ∀ i, ⌜f i⌝ₜ = ⌜g i⌝ₜ) : ⌜f⌝ₜ = ⌜g⌝ₜ := by
  rw [← encode_fin_function_codes f, ← encode_fin_function_codes g]
  simp only [h]

/-- Increasing the bound on stored wire indices does not traverse or change their codes. -/
@[simp high, dominated_expand] theorem encode_fin_castSucc [UniqueEncoding Tree ℕ] {n k : ℕ}
    (f : Fin n → Fin k) :
    ⌜Fin.castSucc ∘ f⌝ₜ = ⌜f⌝ₜ :=
  encode_fin_function_congr _ _ fun _ => rfl

/-- An entry of a table is part of the table's code. -/
@[dominated] theorem size_encode_fin_apply_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (i : Fin n) : ⌜f i⌝ₜ.size ≤ ⌜f⌝ₜ.size :=
  size_encode_le_list_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- The code of an entry of a table is a subtree of the table's code, at a path fixed by its
index. -/
theorem encode_fin_apply {α : Type*} [UniqueEncoding Tree α] {n : ℕ} (f : Fin n → α)
    (i : Fin n) : ⌜f i⌝ₜ = ⌜f⌝ₜ.subtree (List.replicate i.val true ++ [false]) := by
  rw [encode_fin_function]
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, encode_list_cons]
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun j => f j.succ) i

/-- An index stored in a table, as a number, fits in the table. -/
@[dominated] theorem size_encode_val_apply_le [UniqueEncoding Tree ℕ] {n m : ℕ}
    (f : Fin n → Fin m) (i : Fin n) :
    ⌜(f i).val⌝ₜ.size ≤ ⌜f⌝ₜ.size :=
  size_encode_fin_apply_le f i

@[dominated] theorem card_le_size_encode_fin_function {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) : n ≤ ⌜f⌝ₜ.size := by
  simp only [encode_fin_function, size_encode_list, List.length_ofFn]
  omega

theorem size_encode_fin_function_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (bound : ℕ) (h : ∀ i, ⌜f i⌝ₜ.size ≤ bound) :
    ⌜f⌝ₜ.size ≤ n * (bound + 1) + 1 := by
  simpa only [encode_fin_function, List.length_ofFn] using size_encode_list_le (List.ofFn f) bound
    (by simpa only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff] using h)

/-- A composed table stores one selected output for each entry of the first table. -/
@[dominated] theorem size_encode_fin_comp_le {α : Type*} [UniqueEncoding Tree ℕ]
    [UniqueEncoding Tree α] {n m : ℕ} (f : Fin n → Fin m) (g : Fin m → α) :
    ⌜g ∘ f⌝ₜ.size ≤ ⌜f⌝ₜ.size * (⌜g⌝ₜ.size + 1) + 1 :=
  (size_encode_fin_function_le (g ∘ f) ⌜g⌝ₜ.size
    (fun i => size_encode_fin_apply_le g (f i))).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (card_le_size_encode_fin_function f)) 1)

end Complexity
