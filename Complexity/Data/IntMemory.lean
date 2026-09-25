/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.NatMemory

/-!
# Array-backed memory indexed by integers

`IntMemory α` consists of two `NatMemory α` values, following the constructors of `Int`:
`Int.ofNat n` uses `nonneg[n]`, while `Int.negSucc n` uses `neg[n]`.
Thus the two arrays begin at addresses `0` and `-1`, respectively.
-/

@[expose] public section

namespace Complexity

/-- Finitely supported memory on `ℤ`, split into its nonnegative and negative addresses. -/
structure IntMemory (α : Type*) [Inhabited α] where
  /-- Values at `Int.ofNat n`. -/
  nonneg : NatMemory α
  /-- Values at `Int.negSucc n`, that is, `-(n + 1)`. -/
  neg : NatMemory α

namespace IntMemory

variable {α : Type*} [Inhabited α]

instance : GetElem (IntMemory α) ℤ α (fun _ _ ↦ True) where
  getElem m i _ := match i with
    | .ofNat n => m.nonneg[n]
    | .negSucc n => m.neg[n]

theorem getElem_ofNat (m : IntMemory α) (n : ℕ) : m[Int.ofNat n] = m.nonneg[n] := rfl

@[simp]
theorem getElem_natCast (m : IntMemory α) (n : ℕ) : m[(n : ℤ)] = m.nonneg[n] := rfl

@[simp]
theorem getElem_negSucc (m : IntMemory α) (n : ℕ) : m[Int.negSucc n] = m.neg[n] := rfl

@[ext]
theorem ext {m n : IntMemory α} (h : ∀ i : ℤ, m[i] = n[i]) : m = n := by
  obtain ⟨a, b⟩ := m
  obtain ⟨c, e⟩ := n
  have h₁ : a = c := NatMemory.ext fun i ↦ h (.ofNat i)
  have h₂ : b = e := NatMemory.ext fun i ↦ h (.negSucc i)
  cases h₁
  cases h₂
  rfl

instance : EmptyCollection (IntMemory α) := ⟨⟨∅, ∅⟩⟩

instance : Inhabited (IntMemory α) := ⟨∅⟩

@[simp]
theorem nonneg_empty : (∅ : IntMemory α).nonneg = ∅ := rfl

@[simp]
theorem neg_empty : (∅ : IntMemory α).neg = ∅ := rfl

@[simp]
theorem getElem_empty (i : ℤ) : (∅ : IntMemory α)[i] = default := by
  cases i <;> simp

@[simp]
theorem getElem_default (i : ℤ) : (default : IntMemory α)[i] = default :=
  getElem_empty i

/-- Store an array starting at address zero; all other addresses contain `default`. -/
def ofArray (xs : Array α) : IntMemory α :=
  ⟨NatMemory.ofArray xs, ∅⟩

@[simp]
theorem nonneg_ofArray (xs : Array α) : (ofArray xs).nonneg = NatMemory.ofArray xs := rfl

@[simp]
theorem neg_ofArray (xs : Array α) : (ofArray xs).neg = ∅ := rfl

theorem getElem_ofArray_natCast (xs : Array α) (n : ℕ) :
    (ofArray xs)[(n : ℤ)] = xs[n]?.getD default := rfl

theorem getElem_ofArray_negSucc (xs : Array α) (n : ℕ) :
    (ofArray xs)[Int.negSucc n] = default := by
  simp [ofArray]

@[simp]
theorem ofArray_empty : ofArray (α := α) #[] = ∅ := rfl

/-- Only finitely many addresses contain a value different from the default. -/
theorem finite_support (m : IntMemory α) : Set.Finite {i : ℤ | m[i] ≠ default} := by
  apply ((m.nonneg.finite_support.image Int.ofNat).union
    (m.neg.finite_support.image Int.negSucc)).subset
  intro i hi
  cases i with
  | ofNat n => exact Or.inl ⟨n, hi, rfl⟩
  | negSucc n => exact Or.inr ⟨n, hi, rfl⟩

section Map

variable {β γ : Type*} [Inhabited β] [Inhabited γ]

/-- Apply a default-preserving function on both sides of address zero. -/
def map (f : α → β) (hf : f default = default) (m : IntMemory α) : IntMemory β :=
  ⟨NatMemory.map f hf m.nonneg, NatMemory.map f hf m.neg⟩

@[simp]
theorem nonneg_map (f : α → β) (hf : f default = default) (m : IntMemory α) :
    (map f hf m).nonneg = NatMemory.map f hf m.nonneg := rfl

@[simp]
theorem neg_map (f : α → β) (hf : f default = default) (m : IntMemory α) :
    (map f hf m).neg = NatMemory.map f hf m.neg := rfl

@[simp]
theorem getElem_map (f : α → β) (hf : f default = default) (m : IntMemory α) (i : ℤ) :
    (map f hf m)[i] = f m[i] := by
  cases i <;> simp

@[simp]
theorem map_empty (f : α → β) (hf : f default = default) : map f hf ∅ = ∅ := by
  ext i
  simp [hf]

@[simp]
theorem map_ofArray (f : α → β) (hf : f default = default) (xs : Array α) :
    map f hf (ofArray xs) = ofArray (xs.map f) := by
  simp [map, ofArray]

@[simp]
theorem map_id (m : IntMemory α) : map id rfl m = m := by
  ext i
  simp

@[simp]
theorem map_map (f : α → β) (hf : f default = default)
    (g : β → γ) (hg : g default = default) (m : IntMemory α) :
    map g hg (map f hf m) = map (g ∘ f) (by simp [hf, hg]) m := by
  ext i
  simp

end Map

/-- Set a value at any integer address. -/
def set (m : IntMemory α) (i : ℤ) (a : α) : IntMemory α :=
  match i with
  | .ofNat n => { m with nonneg := m.nonneg.set n a }
  | .negSucc n => { m with neg := m.neg.set n a }

theorem getElem_set (m : IntMemory α) (i : ℤ) (a : α) (j : ℤ) :
    (m.set i a)[j] = if i = j then a else m[j] := by
  cases i <;> cases j <;> simp [set, Int.ofNat_inj, NatMemory.getElem_set]

@[simp]
theorem getElem_set_self (m : IntMemory α) (i : ℤ) (a : α) : (m.set i a)[i] = a := by
  simp [getElem_set]

@[simp]
theorem getElem_set_of_ne (m : IntMemory α) {i j : ℤ} (a : α) (h : i ≠ j) :
    (m.set i a)[j] = m[j] := by
  simp [getElem_set, h]

@[simp]
theorem set_getElem (m : IntMemory α) (i : ℤ) : m.set i m[i] = m := by
  ext j
  by_cases h : i = j <;> simp [h]

@[simp]
theorem set_set (m : IntMemory α) (i : ℤ) (a b : α) :
    (m.set i a).set i b = m.set i b := by
  ext j
  by_cases h : i = j <;> simp [h]

theorem set_comm (m : IntMemory α) {i j : ℤ} (a b : α) (h : i ≠ j) :
    (m.set i a).set j b = (m.set j b).set i a := by
  ext k
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

@[simp]
theorem map_set {β : Type*} [Inhabited β] (f : α → β) (hf : f default = default)
    (m : IntMemory α) (i : ℤ) (a : α) :
    map f hf (m.set i a) = (map f hf m).set i (f a) := by
  ext j
  by_cases h : i = j <;> simp [h]

end IntMemory

end Complexity
