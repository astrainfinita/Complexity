/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Basic
public import Complexity.Asymptotics.Basic

/-!
# Models of time- and space-bounded computation

A model specifies admissible input/output behaviors and an input-size function.
Each behavior belongs to one fixed computation across all inputs and budgets.
Time and space are upper bounds, witnessed jointly by that computation.

The common resource predicate accepts budgets `α → Data → ℕ`. Ordinary specifications
specialize these to `α → ℕ`, shared by every legal code of a value, and
`ComputableWithGrowth` uses one all-input coefficient for each resource. A value with
unbounded processing costs over its codes cannot satisfy a finite value-indexed budget.
Complexity classes measure actual code sizes at their own boundary.
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

/-- One behavior handles all valid codes with joint budgets depending on both the
input value and its actual representation. Mentioning the value in a mathematical
budget does not give the machine a free decoding operation. -/
def ComputableWithCodeBudgets (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : α → Data → ℕ) : Prop :=
  ∃ R ∈ model.behaviors,
    Encoding.Computes f fun a src dst =>
      R src (pure dst) (t a src) (s a src)

/-- Value budgets uniformly cover every legal representation of that value. -/
def ComputableWithin (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : α → ℕ) : Prop :=
  model.ComputableWithCodeBudgets f (fun a _ => t a) (fun a _ => s a)

def ComputableInTime (model : TimeSpaceModel Id Data) (f : α → β) (t : α → ℕ) : Prop :=
  ∃ s, model.ComputableWithin f t s

def ComputableInSpace (model : TimeSpaceModel Id Data) (f : α → β) (s : α → ℕ) : Prop :=
  ∃ t, model.ComputableWithin f t s

/-- A single behavior satisfies both all-input growth bounds. Correctness and termination
hold at every input, including where either target budget is zero. -/
def ComputableWithGrowth (model : TimeSpaceModel Id Data) (f : α → β)
    (T S : α → ℕ) : Prop :=
  ∃ t s, model.ComputableWithin f t s ∧ Dominated t T ∧ Dominated s S

variable {model : TimeSpaceModel Id Data} {f : α → β} {t s t' s' : α → ℕ}

theorem ComputableWithCodeBudgets.mono {t s t' s' : α → Data → ℕ}
    (h : model.ComputableWithCodeBudgets f t s)
    (ht : ∀ a src, t a src ≤ t' a src)
    (hs : ∀ a src, s a src ≤ s' a src) :
    model.ComputableWithCodeBudgets f t' s' := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.mono (fun hc => model.budget_mono hR hc (ht _ _) (hs _ _))⟩

theorem ComputableWithin.mono (h : model.ComputableWithin f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    model.ComputableWithin f t' s' :=
  ComputableWithCodeBudgets.mono h (fun a _ => ht a) (fun a _ => hs a)

theorem ComputableWithin.computableInTime
    (h : model.ComputableWithin f t s) : model.ComputableInTime f t := ⟨s, h⟩

theorem ComputableWithin.computableInSpace
    (h : model.ComputableWithin f t s) : model.ComputableInSpace f s := ⟨t, h⟩

theorem ComputableInTime.mono (h : model.ComputableInTime f t)
    (ht : ∀ a, t a ≤ t' a) : model.ComputableInTime f t' := by
  obtain ⟨s, h⟩ := h
  exact ⟨s, h.mono ht (fun _ => le_rfl)⟩

theorem ComputableInSpace.mono (h : model.ComputableInSpace f s)
    (hs : ∀ a, s a ≤ s' a) : model.ComputableInSpace f s' := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.mono (fun _ => le_rfl) hs⟩

theorem ComputableWithin.computableWithGrowth
    (h : model.ComputableWithin f t s) : model.ComputableWithGrowth f t s :=
  ⟨t, s, h, Dominated.refl _, Dominated.refl _⟩

theorem ComputableWithGrowth.mono (h : model.ComputableWithGrowth f t s)
    (ht : Dominated t t') (hs : Dominated s s') : model.ComputableWithGrowth f t' s' := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨u, v, h, hu.trans ht, hv.trans hs⟩

end TimeSpaceModel

theorem TimeSpaceModel.ComputableWithCodeBudgets.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : α → Data → ℕ}
    (h : model.ComputableWithCodeBudgets g t s)
    (hfg : ∀ a, encode Data (f a) = encode Data (g a)) :
    model.ComputableWithCodeBudgets f t s := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.of_encode hfg⟩

theorem TimeSpaceModel.ComputableWithin.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : α → ℕ}
    (h : model.ComputableWithin g t s)
    (hfg : ∀ a, encode Data (f a) = encode Data (g a)) :
    model.ComputableWithin f t s :=
  TimeSpaceModel.ComputableWithCodeBudgets.of_encode h hfg

end Complexity
