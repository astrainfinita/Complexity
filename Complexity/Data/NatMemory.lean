/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Array-backed memory indexed by natural numbers

`NatMemory α` is an array modulo equality of `fun i ↦ xs[i]?.getD default`.
Every address is valid, and all but finitely many addresses contain `default`.
In particular, trailing default values do not affect equality.

The interface describes storage only: there is no distinguished address or access order.
-/

@[expose] public section

namespace Complexity

/-- Finitely supported memory on `ℕ`, with default value `default`, represented by an array. -/
def NatMemory (α : Type*) [Inhabited α] :=
  Quotient (Setoid.ker fun xs : Array α ↦ fun i : ℕ ↦ xs[i]?.getD default)

namespace NatMemory

variable {α : Type*} [Inhabited α]

/-- Interpret an array as memory, returning `default` beyond its end. -/
def ofArray (xs : Array α) : NatMemory α :=
  Quotient.mk _ xs

instance : GetElem (NatMemory α) ℕ α (fun _ _ ↦ True) where
  getElem m i _ := Setoid.kerLift (fun xs : Array α ↦ fun j : ℕ ↦ xs[j]?.getD default) m i

@[simp]
theorem getElem_ofArray (xs : Array α) (i : ℕ) :
    (ofArray xs)[i] = xs[i]?.getD default :=
  rfl

@[ext]
theorem ext {m n : NatMemory α} (h : ∀ i : ℕ, m[i] = n[i]) : m = n :=
  Setoid.kerLift_injective _ (funext h)

theorem ofArray_eq_iff {xs ys : Array α} :
    ofArray xs = ofArray ys ↔ ∀ i : ℕ, xs[i]?.getD default = ys[i]?.getD default := by
  constructor
  · intro h i
    exact congrArg (fun m : NatMemory α ↦ m[i]) h
  · intro h
    apply ext
    exact h

/-- Prove a property of memory by choosing an array representative. -/
@[elab_as_elim]
protected theorem induction_on {p : NatMemory α → Prop} (m : NatMemory α)
    (h : ∀ xs, p (ofArray xs)) : p m :=
  Quotient.inductionOn m h

instance : EmptyCollection (NatMemory α) := ⟨ofArray #[]⟩

instance : Inhabited (NatMemory α) := ⟨∅⟩

@[simp]
theorem ofArray_empty : ofArray (α := α) #[] = ∅ := rfl

@[simp]
theorem getElem_empty (i : ℕ) : (∅ : NatMemory α)[i] = default := by
  simp [← ofArray_empty]

@[simp]
theorem getElem_default (i : ℕ) : (default : NatMemory α)[i] = default :=
  getElem_empty i

private theorem getD_append_replicate (xs : Array α) (n i : ℕ) :
    (xs ++ Array.replicate n default)[i]?.getD default = xs[i]?.getD default := by
  by_cases h : i < xs.size
  · rw [Array.getElem?_append_left h]
  · rw [Array.getElem?_append_right (by omega),
      Array.getElem?_eq_none (xs := xs) (by omega)]
    simp only [Array.getElem?_replicate]
    split <;> rfl

@[simp]
theorem ofArray_append_replicate (xs : Array α) (n : ℕ) :
    ofArray (xs ++ Array.replicate n default) = ofArray xs := by
  ext i
  exact getD_append_replicate xs n i

@[simp]
theorem ofArray_replicate (n : ℕ) : ofArray (Array.replicate n (default : α)) = ∅ := by
  simpa using ofArray_append_replicate (α := α) #[] n

@[simp]
theorem ofArray_push_default (xs : Array α) : ofArray (xs.push default) = ofArray xs := by
  simpa using ofArray_append_replicate xs 1

/-- Beyond some address, every value is `default`. -/
theorem exists_forall_ge (m : NatMemory α) : ∃ n : ℕ, ∀ i ≥ n, m[i] = default := by
  induction m using NatMemory.induction_on with
  | h xs =>
    exact ⟨xs.size, fun i hi ↦ by simp [Array.getElem?_eq_none hi]⟩

/-- Only finitely many addresses contain a value different from the default. -/
theorem finite_support (m : NatMemory α) : Set.Finite {i : ℕ | m[i] ≠ default} := by
  obtain ⟨n, hn⟩ := m.exists_forall_ge
  exact (Set.finite_lt_nat n).subset fun i hi ↦ Nat.lt_of_not_ge fun h ↦ hi (hn i h)

section Map

variable {β γ : Type*} [Inhabited β] [Inhabited γ]

private theorem getD_map (f : α → β) (hf : f default = default) (xs : Array α) (i : ℕ) :
    (xs.map f)[i]?.getD default = f (xs[i]?.getD default) := by
  rw [Array.getElem?_map]
  cases xs[i]? <;> simp [hf]

/-- Apply a function to every stored value, preserving the default outside finite storage. -/
def map (f : α → β) (hf : f default = default) (m : NatMemory α) : NatMemory β :=
  Quotient.map (fun xs ↦ xs.map f) (fun xs ys h ↦ by
    funext i
    change (xs.map f)[i]?.getD default = (ys.map f)[i]?.getD default
    rw [getD_map f hf, getD_map f hf]
    exact congrArg f (congrFun h i)) m

@[simp]
theorem map_ofArray (f : α → β) (hf : f default = default) (xs : Array α) :
    map f hf (ofArray xs) = ofArray (xs.map f) := rfl

@[simp]
theorem getElem_map (f : α → β) (hf : f default = default) (m : NatMemory α) (i : ℕ) :
    (map f hf m)[i] = f m[i] := by
  induction m using NatMemory.induction_on with
  | h xs => exact getD_map f hf xs i

@[simp]
theorem map_empty (f : α → β) (hf : f default = default) : map f hf ∅ = ∅ := by
  ext i
  simp [hf]

@[simp]
theorem map_id (m : NatMemory α) : map id rfl m = m := by
  ext i
  simp

@[simp]
theorem map_map (f : α → β) (hf : f default = default)
    (g : β → γ) (hg : g default = default) (m : NatMemory α) :
    map g hg (map f hf m) = map (g ∘ f) (by simp [hf, hg]) m := by
  ext i
  simp

end Map

/-- Update an array, first extending it with default values when necessary. -/
def setArray (xs : Array α) (i : ℕ) (a : α) : Array α :=
  if h : i < xs.size then xs.set i a else
    (xs ++ Array.replicate (i + 1 - xs.size) default).set i a (by simp; omega)

private theorem getD_setArray (xs : Array α) (i : ℕ) (a : α) (j : ℕ) :
    (setArray xs i a)[j]?.getD default = if i = j then a else xs[j]?.getD default := by
  unfold setArray
  split <;> rw [Array.getElem?_set]
  · split <;> rfl
  · split
    · rfl
    · exact getD_append_replicate xs _ j

/-- Set a value at any address, extending the underlying array if needed. -/
def set (m : NatMemory α) (i : ℕ) (a : α) : NatMemory α :=
  Quotient.map (fun xs ↦ setArray xs i a) (fun xs ys h ↦ by
    funext j
    simp only [getD_setArray]
    split
    · rfl
    · exact congrFun h j) m

theorem getElem_set (m : NatMemory α) (i : ℕ) (a : α) (j : ℕ) :
    (m.set i a)[j] = if i = j then a else m[j] := by
  induction m using NatMemory.induction_on with
  | h xs => exact getD_setArray xs i a j

@[simp]
theorem getElem_set_self (m : NatMemory α) (i : ℕ) (a : α) : (m.set i a)[i] = a := by
  simp [getElem_set]

@[simp]
theorem getElem_set_of_ne (m : NatMemory α) {i j : ℕ} (a : α) (h : i ≠ j) :
    (m.set i a)[j] = m[j] := by
  simp [getElem_set, h]

@[simp]
theorem set_getElem (m : NatMemory α) (i : ℕ) : m.set i m[i] = m := by
  ext j
  by_cases h : i = j <;> simp [h]

@[simp]
theorem set_set (m : NatMemory α) (i : ℕ) (a b : α) :
    (m.set i a).set i b = m.set i b := by
  ext j
  by_cases h : i = j <;> simp [h]

theorem set_comm (m : NatMemory α) {i j : ℕ} (a b : α) (h : i ≠ j) :
    (m.set i a).set j b = (m.set j b).set i a := by
  ext k
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

@[simp]
theorem map_set {β : Type*} [Inhabited β] (f : α → β) (hf : f default = default)
    (m : NatMemory α) (i : ℕ) (a : α) :
    map f hf (m.set i a) = (map f hf m).set i (f a) := by
  ext j
  by_cases h : i = j <;> simp [h]

end NatMemory

end Complexity
