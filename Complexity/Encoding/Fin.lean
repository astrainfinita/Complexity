/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn

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

end Complexity
