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
specialize these to `α → ℕ`, shared by every legal code of a value, and `ComputableIn` states
properties of these budgets, such as `IsO(T)` for one all-input coefficient for each resource.
A value with unbounded processing costs over its codes cannot satisfy a finite value-indexed
budget.
`ComputableWithinBySize` instead measures the size of the actual input code, as
complexity classes do at their boundary.
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
def ComputableWithinByCode (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : α → Data → ℕ) : Prop :=
  ∃ R ∈ model.behaviors,
    Encoding.Computes f fun a src dst =>
      R src (pure dst) (t a src) (s a src)

/-- Value budgets uniformly cover every legal representation of that value. -/
def ComputableWithin (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : α → ℕ) : Prop :=
  model.ComputableWithinByCode f (fun a _ => t a) (fun a _ => s a)

/-- `f` is computable within a time budget with property `time` and a space budget with
property `space`, by a single behavior on every input. `model.ComputableIn f IsO(T) IsO(S)` is
computability in time `O(T a)` and space `O(S a)`, each up to one coefficient for all inputs;
the space is unrestricted by default. Correctness and termination hold at every input,
including where a budget is zero. -/
def ComputableIn (model : TimeSpaceModel Id Data) (f : α → β)
    (time : (α → ℕ) → Prop) (space : (α → ℕ) → Prop := fun _ => True) : Prop :=
  ∃ t s, model.ComputableWithin f t s ∧ time t ∧ space s

/-- Budgets at the complexity boundary depend on the size of the actual input code.
This does not require unique encodings or assign a canonical size to an abstract value. -/
def ComputableWithinBySize (model : TimeSpaceModel Id Data) (f : α → β)
    (t s : ℕ → ℕ) : Prop :=
  model.ComputableWithinByCode f
    (fun _ src => t (model.inputSize src))
    (fun _ src => s (model.inputSize src))

variable {model : TimeSpaceModel Id Data} {f : α → β} {t s t' s' : α → ℕ}

theorem ComputableWithinByCode.mono {t s t' s' : α → Data → ℕ}
    (h : model.ComputableWithinByCode f t s)
    (ht : ∀ a src, t a src ≤ t' a src)
    (hs : ∀ a src, s a src ≤ s' a src) :
    model.ComputableWithinByCode f t' s' := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.mono (fun hc => model.budget_mono hR hc (ht _ _) (hs _ _))⟩

theorem ComputableWithin.mono (h : model.ComputableWithin f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    model.ComputableWithin f t' s' :=
  ComputableWithinByCode.mono h (fun a _ => ht a) (fun a _ => hs a)

theorem ComputableWithinBySize.mono {t s t' s' : ℕ → ℕ}
    (h : model.ComputableWithinBySize f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    model.ComputableWithinBySize f t' s' :=
  ComputableWithinByCode.mono h (fun _ r => ht (model.inputSize r))
    (fun _ r => hs (model.inputSize r))

theorem ComputableWithin.computableIn
    (h : model.ComputableWithin f t s) : model.ComputableIn f IsO(t) IsO(s) :=
  ⟨t, s, h, Dominated.refl _, Dominated.refl _⟩

theorem ComputableIn.mono {time space time' space' : (α → ℕ) → Prop}
    (h : model.ComputableIn f time space)
    (ht : ∀ t, time t → time' t) (hs : ∀ s, space s → space' s) :
    model.ComputableIn f time' space' := by
  obtain ⟨t, s, h, htime, hspace⟩ := h
  exact ⟨t, s, h, ht t htime, hs s hspace⟩

end TimeSpaceModel

theorem TimeSpaceModel.ComputableWithinByCode.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : α → Data → ℕ}
    (h : model.ComputableWithinByCode g t s)
    (hfg : ∀ a, encode Data (f a) = encode Data (g a)) :
    model.ComputableWithinByCode f t s := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.of_encode hfg⟩

theorem TimeSpaceModel.ComputableWithin.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : α → ℕ}
    (h : model.ComputableWithin g t s)
    (hfg : ∀ a, encode Data (f a) = encode Data (g a)) :
    model.ComputableWithin f t s :=
  TimeSpaceModel.ComputableWithinByCode.of_encode h hfg

/-- Equal output codes preserve the same size-indexed resource certificate. -/
theorem TimeSpaceModel.ComputableWithinBySize.of_encode {Data α β γ : Type*}
    [Encoding Data α] [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {t s : ℕ → ℕ}
    (h : model.ComputableWithinBySize g t s)
    (hfg : ∀ a, encode Data (f a) = encode Data (g a)) :
    model.ComputableWithinBySize f t s :=
  TimeSpaceModel.ComputableWithinByCode.of_encode h hfg

namespace TimeSpaceModel

variable {Data α β : Type*} [UniqueEncoding Data α] [Encoding Data β]
  {model : TimeSpaceModel Id Data} {f : α → β} {T S : ℕ → ℕ}

/-- With unique input encodings, a value budget obtained from that encoding's size
is exactly the corresponding actual-code-size budget. -/
theorem ComputableWithin.iff_bySize :
    model.ComputableWithin f
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a))) ↔
    model.ComputableWithinBySize f T S := by
  constructor <;> rintro ⟨R, hR, h⟩ <;> refine ⟨R, hR, ?_⟩
  all_goals
    intro a src ha
    obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
    exact h a _ (by simp)

end TimeSpaceModel

end Complexity
