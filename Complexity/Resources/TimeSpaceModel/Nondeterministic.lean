/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Mathlib.Data.Multiset.Basic

/-!
# Nondeterministic decision bounds

A behavior supplies the complete multiset of branch outputs within joint resource
bounds. Every output must decode as a Boolean; acceptance means some output decodes
as `true`. Invalid input codes impose no obligations.
-/

@[expose] public section

namespace Complexity

/-- A complete multiset of branch outputs decides `p`: every output decodes as a Boolean,
and some output decodes as `true` exactly when `p` holds. The additional condition refers
to that same multiset, including rejecting branches and their multiplicities. -/
def Encoding.NDecides {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
    (p : α → Prop) (P : α → Data → Multiset Data → Prop) : Prop :=
  ∀ a src, a ∈ decode α src →
    ∃ outs, P a src outs ∧
      (∀ dst ∈ outs, (decode Bool dst).Dom) ∧
      ((∃ dst ∈ outs, true ∈ decode Bool dst) ↔ p a)

namespace Encoding.NDecides

variable {Data α : Type*} [Encoding Data Bool] {p : α → Prop}
  {P Q : α → Data → Multiset Data → Prop}

theorem mono [Encoding Data α] (h : NDecides p P)
    (hPQ : ∀ {a src outs}, P a src outs → Q a src outs) : NDecides p Q := by
  intro a src hsrc
  obtain ⟨outs, hP, hvalid, haccept⟩ := h a src hsrc
  exact ⟨outs, hPQ hP, hvalid, haccept⟩

theorem iff_of_uniqueInput [UniqueEncoding Data α] :
    NDecides p P ↔ ∀ a,
      ∃ outs, P a (encode Data a) outs ∧
        (∀ dst ∈ outs, (decode Bool dst).Dom) ∧
        ((∃ dst ∈ outs, true ∈ decode Bool dst) ↔ p a) := by
  simp only [NDecides, UniqueEncoding.mem_decode_iff, forall_eq']

end Encoding.NDecides

namespace TimeSpaceModel

section InputBudgets

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]

/-- One behavior decides every legal representation with budgets indexed by both the
input value and its actual code. The complete branch multiset is retained. -/
def NDecidableWithinByCode (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t s : α → Data → ℕ) : Prop :=
  ∃ R ∈ model.behaviors, Encoding.NDecides p fun a src outs =>
    R src outs (t a src) (s a src)

/-- Value-indexed budgets uniformly cover all legal representations of each value. -/
def NDecidableWithin (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t s : α → ℕ) : Prop :=
  model.NDecidableWithinByCode p (fun a _ => t a) (fun a _ => s a)

/-- `p` is decidable nondeterministically within time `O(T a)` and space `O(S a)` on every
input `a`: both bounds use the same nondeterministic behavior, and every branch must still
terminate within its resource bounds. -/
def NDecidableInO (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (T S : α → ℕ) : Prop :=
  ∃ t s, model.NDecidableWithin p t s ∧ Dominated t T ∧ Dominated s S

/-- Code-length budgets for one complete nondeterministic computation. Both resources
refer to the actual input representation, independently of its decoded value. -/
def NDecidableWithinBySize (model : TimeSpaceModel Multiset Data)
    (p : α → Prop) (t s : ℕ → ℕ) : Prop :=
  model.NDecidableWithinByCode p
    (fun _ src => t (model.inputSize src))
    (fun _ src => s (model.inputSize src))

variable {model : TimeSpaceModel Multiset Data} {p q : α → Prop} {t s t' s' : α → ℕ}

theorem NDecidableWithinByCode.mono {t s t' s' : α → Data → ℕ}
    (h : model.NDecidableWithinByCode p t s)
    (ht : ∀ a src, t a src ≤ t' a src)
    (hs : ∀ a src, s a src ≤ s' a src) :
    model.NDecidableWithinByCode p t' s' := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.mono fun hrun =>
    model.budget_mono hR hrun (ht _ _) (hs _ _)⟩

theorem NDecidableWithinByCode.congr {t s : α → Data → ℕ}
    (h : model.NDecidableWithinByCode p t s) (hp : ∀ a, p a ↔ q a) :
    model.NDecidableWithinByCode q t s :=
  funext (fun a => propext (hp a)) ▸ h

theorem NDecidableWithin.mono (h : model.NDecidableWithin p t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    model.NDecidableWithin p t' s' :=
  NDecidableWithinByCode.mono h (fun a _ => ht a) (fun a _ => hs a)

theorem NDecidableWithin.congr (h : model.NDecidableWithin p t s)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableWithin q t s :=
  NDecidableWithinByCode.congr h hp

theorem NDecidableWithin.nDecidableInO
    (h : model.NDecidableWithin p t s) : model.NDecidableInO p t s :=
  ⟨t, s, h, Dominated.refl _, Dominated.refl _⟩

theorem NDecidableInO.mono (h : model.NDecidableInO p t s)
    (ht : Dominated t t') (hs : Dominated s s') : model.NDecidableInO p t' s' := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨u, v, h, hu.trans ht, hv.trans hs⟩

theorem NDecidableWithinBySize.mono {t s t' s' : ℕ → ℕ}
    (h : model.NDecidableWithinBySize p t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    model.NDecidableWithinBySize p t' s' :=
  NDecidableWithinByCode.mono h (fun _ src => ht (model.inputSize src))
    (fun _ src => hs (model.inputSize src))

theorem NDecidableWithinBySize.congr {t s : ℕ → ℕ}
    (h : model.NDecidableWithinBySize p t s)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableWithinBySize q t s :=
  NDecidableWithinByCode.congr h hp

end InputBudgets

section UniqueInput

variable {Data α : Type*} [UniqueEncoding Data α] [Encoding Data Bool]
  {model : TimeSpaceModel Multiset Data} {p : α → Prop} {T S : ℕ → ℕ}

/-- With unique input encodings, value budgets obtained from encoding size are exactly
actual-code-size budgets; the complete branch specification is unchanged. -/
theorem NDecidableWithin.iff_bySize :
    model.NDecidableWithin p
      (fun a => T (model.inputSize (encode Data a)))
      (fun a => S (model.inputSize (encode Data a))) ↔
    model.NDecidableWithinBySize p T S := by
  constructor <;> rintro ⟨R, hR, h⟩ <;> refine ⟨R, hR, ?_⟩
  all_goals
    intro a src hsrc
    obtain rfl := UniqueEncoding.mem_decode_iff.mp hsrc
    exact h a _ (by simp)

end UniqueInput

end TimeSpaceModel

end Complexity
