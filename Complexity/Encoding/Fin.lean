/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange

/-! # Encodings of bounded indices and finite tuples -/

@[expose] public section

namespace Complexity

/-- A bounded index uses its natural-number code. -/
instance {R : Type*} [c : UniqueEncoding R ℕ] {n : ℕ} : UniqueEncoding R (Fin n) :=
  (c.subtype (· < n)).ofEquiv Fin.equivSubtype

@[simp high] theorem encode_fin {R : Type*} [UniqueEncoding R ℕ] {n : ℕ} (i : Fin n) :
    encode R i = encode R i.val := rfl

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

/-- Appending a tuple entry uses the ordinary list representation. -/
@[simp high] theorem encode_fin_snoc {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (a : α) : ⌜Fin.snoc f a⌝ₜ = ⌜List.ofFn f ++ [a]⌝ₜ := by
  rw [encode_fin_function, List.ofFn_succ']
  simp

/-- Erasing bounds from a tuple of wire indices does not change its representation. -/
@[simp high] theorem encode_fin_values [UniqueEncoding Tree ℕ] {n k : ℕ}
    (f : Fin k → Fin n) : ⌜List.ofFn (Fin.val ∘ f)⌝ₜ = ⌜List.ofFn f⌝ₜ := by
  simp only [← List.map_ofFn]
  exact encode_list_map_of_encode Fin.val (fun _ => rfl) _

@[simp] theorem encode_finRange [UniqueEncoding Tree ℕ] (n : ℕ) :
    ⌜List.finRange n⌝ₜ = ⌜List.range n⌝ₜ := by
  rw [← List.map_coe_finRange_eq_range, ← List.ofFn_id]
  simpa only [List.map_ofFn] using (encode_fin_values (id : Fin n → Fin n)).symm

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
@[simp high] theorem encode_fin_castSucc [UniqueEncoding Tree ℕ] {n k : ℕ}
    (f : Fin n → Fin k) :
    ⌜Fin.castSucc ∘ f⌝ₜ = ⌜f⌝ₜ :=
  encode_fin_function_congr _ _ fun _ => rfl

theorem size_encode_fin_apply_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (i : Fin n) : ⌜f i⌝ₜ.size ≤ ⌜f⌝ₜ.size :=
  size_encode_le_list_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem card_le_size_encode_fin_function {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) : n ≤ ⌜f⌝ₜ.size := by
  simp only [encode_fin_function, size_encode_list, List.length_ofFn]
  omega

theorem size_encode_fin_function_le {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (f : Fin n → α) (bound : ℕ) (h : ∀ i, ⌜f i⌝ₜ.size ≤ bound) :
    ⌜f⌝ₜ.size ≤ n * (bound + 1) + 1 := by
  simpa only [encode_fin_function, List.length_ofFn] using size_encode_list_le (List.ofFn f) bound
    (by simpa only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff] using h)

/-- A composed table stores one selected output for each entry of the first table. -/
theorem size_encode_fin_comp_le {α : Type*} [UniqueEncoding Tree ℕ]
    [UniqueEncoding Tree α] {n m : ℕ} (f : Fin n → Fin m) (g : Fin m → α) :
    ⌜g ∘ f⌝ₜ.size ≤ ⌜f⌝ₜ.size * (⌜g⌝ₜ.size + 1) + 1 :=
  (size_encode_fin_function_le (g ∘ f) ⌜g⌝ₜ.size
    (fun i => size_encode_fin_apply_le g (f i))).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (card_le_size_encode_fin_function f)) 1)

end Complexity
