/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Fintype.Inv

/-! # Replacement along finite embeddings

Install a function on an embedded finite domain, retaining the original function elsewhere.
-/

@[expose] public section

namespace Function.Embedding

variable {κ τ σ α : Type*} [Fintype κ] [DecidableEq τ]

/-- Replace the values in the image of an embedding, preserving its complement. -/
def replace (e : κ ↪ τ) (source : κ → α) (target : τ → α) : τ → α :=
  fun j ↦ if h : j ∈ Set.range e then source (e.invOfMemRange ⟨j, h⟩) else target j

@[simp] theorem replace_apply (e : κ ↪ τ) (source : κ → α) (target : τ → α)
    (i : κ) : e.replace source target (e i) = source i := by
  simp [replace]

@[simp] theorem replace_of_not_mem (e : κ ↪ τ) (source : κ → α) (target : τ → α)
    {j : τ} (hj : j ∉ Set.range e) : e.replace source target j = target j := by
  simp [replace, hj]

@[simp] theorem restrict_replace (e : κ ↪ τ) (source : κ → α) (target : τ → α) :
    e.replace source target ∘ e = source := by
  funext i
  exact e.replace_apply source target i

@[simp] theorem replace_restrict (e : κ ↪ τ) (target : τ → α) :
    e.replace (target ∘ e) target = target := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp [hj]

/-- A later replacement overwrites the earlier values on the same embedded domain. -/
@[simp] theorem replace_replace (e : κ ↪ τ) (source next : κ → α) (target : τ → α) :
    e.replace next (e.replace source target) = e.replace next target := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp [hj]

/-- Installing through an intermediate domain agrees with the composed embedding. -/
theorem replace_comp [Fintype τ] [DecidableEq σ] (e : κ ↪ τ) (f : τ ↪ σ)
    (source : κ → α) (target : σ → α) :
    f.replace (e.replace source (target ∘ f)) target = (e.trans f).replace source target := by
  funext j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    by_cases hi : i ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hi
      simpa only [trans_apply, replace_apply] using
        ((e.trans f).replace_apply source target i).symm
    · have h : f i ∉ Set.range (e.trans f) := by
        rintro ⟨a, ha⟩
        exact hi ⟨a, f.injective ha⟩
      rw [replace_apply, replace_of_not_mem _ _ _ hi, replace_of_not_mem _ _ _ h]
      rfl
  · have h : j ∉ Set.range (e.trans f) := by
      rintro ⟨i, rfl⟩
      exact hj ⟨e i, rfl⟩
    rw [replace_of_not_mem _ _ _ hj, replace_of_not_mem _ _ _ h]

end Function.Embedding
