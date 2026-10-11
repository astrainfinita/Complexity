/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Basic

/-!
# Models of time- and space-bounded computation

A model specifies admissible input/output behaviors and an input-size function.
Each behavior belongs to one fixed computation across all inputs and budgets.
Time and space are upper bounds, witnessed jointly by that computation.
-/

@[expose] public section

namespace Complexity

universe u v

/-- Admissible time- and space-bounded input/output behaviors, together with an
input-size function. Concrete realizations are supplied by each model. -/
structure TimeSpaceModel (m : Type u → Type v) (Data : Type u) where
  /-- Size of the actual input representation. -/
  inputSize : Data → ℕ
  /-- Each relation describes one computation across all inputs and budgets. -/
  behaviors : Set (Data → m Data → ℕ → ℕ → Prop)
  /-- Increasing either budget preserves an admissible computation. -/
  budget_mono : ∀ {R}, R ∈ behaviors → ∀ {x y t s t' s'},
    R x y t s → t ≤ t' → s ≤ s' → R x y t' s'

namespace TimeSpaceModel

variable {Data α β : Type*} [Encoding Data α] [Encoding Data β]

/-- One admissible behavior computes the function on every valid input code,
within both pointwise resource bounds. -/
def ComputableInTimeAndSpace (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : ℕ → ℕ) : Prop :=
  ∃ R ∈ model.behaviors, Encoding.Computes (fun x y => R x (pure y)) model.inputSize f t s

/-- Compute a function within a pointwise time bound, with some space bound. -/
def ComputableInTime (model : TimeSpaceModel Id Data) (f : α → β) (t : ℕ → ℕ) : Prop :=
  ∃ s, model.ComputableInTimeAndSpace f t s

/-- Compute a function within a pointwise space bound, with some time bound.
The time bound still requires termination on every valid input. -/
def ComputableInSpace (model : TimeSpaceModel Id Data) (f : α → β) (s : ℕ → ℕ) : Prop :=
  ∃ t, model.ComputableInTimeAndSpace f t s

variable {model : TimeSpaceModel Id Data} {f : α → β} {t s t' s' : ℕ → ℕ}

theorem ComputableInTimeAndSpace.mono (h : model.ComputableInTimeAndSpace f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    model.ComputableInTimeAndSpace f t' s' := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.mono (model.budget_mono hR) ht hs⟩

theorem ComputableInTimeAndSpace.computableInTime
    (h : model.ComputableInTimeAndSpace f t s) : model.ComputableInTime f t :=
  ⟨s, h⟩

theorem ComputableInTimeAndSpace.computableInSpace
    (h : model.ComputableInTimeAndSpace f t s) : model.ComputableInSpace f s :=
  ⟨t, h⟩

theorem ComputableInTime.mono (h : model.ComputableInTime f t)
    (ht : ∀ n, t n ≤ t' n) : model.ComputableInTime f t' := by
  obtain ⟨s, h⟩ := h
  exact ⟨s, h.mono ht (fun _ => le_rfl)⟩

theorem ComputableInSpace.mono (h : model.ComputableInSpace f s)
    (hs : ∀ n, s n ≤ s' n) : model.ComputableInSpace f s' := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.mono (fun _ => le_rfl) hs⟩

end TimeSpaceModel

/-- Changing output values without changing their codes retains one behavior and both budgets. -/
theorem TimeSpaceModel.ComputableInTimeAndSpace.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : ℕ → ℕ}
    (hg : model.ComputableInTimeAndSpace g t s)
    (hfg : ∀ x, encode Data (f x) = encode Data (g x)) :
    model.ComputableInTimeAndSpace f t s := by
  obtain ⟨R, hR, h⟩ := hg
  exact ⟨R, hR, h.of_encode hfg⟩

end Complexity
