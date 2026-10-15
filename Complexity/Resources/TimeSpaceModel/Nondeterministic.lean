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
def NDecidableWithCodeBudgets (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t s : α → Data → ℕ) : Prop :=
  ∃ R ∈ model.behaviors, Encoding.NDecides p fun a src outs =>
    R src outs (t a src) (s a src)

/-- Value-indexed budgets uniformly cover all legal representations of each value. -/
def NDecidableWithin (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t s : α → ℕ) : Prop :=
  model.NDecidableWithCodeBudgets p (fun a _ => t a) (fun a _ => s a)

def NDecidableInTime (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (t : α → ℕ) : Prop := ∃ s, model.NDecidableWithin p t s

def NDecidableInSpace (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (s : α → ℕ) : Prop := ∃ t, model.NDecidableWithin p t s

/-- Both all-input growth budgets use the same nondeterministic behavior; every branch
must still terminate within its resource bounds. -/
def NDecidableWithGrowth (model : TimeSpaceModel Multiset Data) (p : α → Prop)
    (T S : α → ℕ) : Prop :=
  ∃ t s, model.NDecidableWithin p t s ∧ Dominated t T ∧ Dominated s S

variable {model : TimeSpaceModel Multiset Data} {p q : α → Prop} {t s t' s' : α → ℕ}

theorem NDecidableWithCodeBudgets.mono {t s t' s' : α → Data → ℕ}
    (h : model.NDecidableWithCodeBudgets p t s)
    (ht : ∀ a src, t a src ≤ t' a src)
    (hs : ∀ a src, s a src ≤ s' a src) :
    model.NDecidableWithCodeBudgets p t' s' := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h.mono fun hrun =>
    model.budget_mono hR hrun (ht _ _) (hs _ _)⟩

theorem NDecidableWithCodeBudgets.congr {t s : α → Data → ℕ}
    (h : model.NDecidableWithCodeBudgets p t s) (hp : ∀ a, p a ↔ q a) :
    model.NDecidableWithCodeBudgets q t s :=
  funext (fun a => propext (hp a)) ▸ h

theorem NDecidableWithin.mono (h : model.NDecidableWithin p t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    model.NDecidableWithin p t' s' :=
  NDecidableWithCodeBudgets.mono h (fun a _ => ht a) (fun a _ => hs a)

theorem NDecidableWithin.nDecidableInTime
    (h : model.NDecidableWithin p t s) : model.NDecidableInTime p t := ⟨s, h⟩

theorem NDecidableWithin.nDecidableInSpace
    (h : model.NDecidableWithin p t s) : model.NDecidableInSpace p s := ⟨t, h⟩

theorem NDecidableWithin.congr (h : model.NDecidableWithin p t s)
    (hp : ∀ a, p a ↔ q a) : model.NDecidableWithin q t s :=
  NDecidableWithCodeBudgets.congr h hp

theorem NDecidableWithin.nDecidableWithGrowth
    (h : model.NDecidableWithin p t s) : model.NDecidableWithGrowth p t s :=
  ⟨t, s, h, Dominated.refl _, Dominated.refl _⟩

theorem NDecidableWithGrowth.mono (h : model.NDecidableWithGrowth p t s)
    (ht : Dominated t t') (hs : Dominated s s') : model.NDecidableWithGrowth p t' s' := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨u, v, h, hu.trans ht, hv.trans hs⟩

end InputBudgets

end TimeSpaceModel

end Complexity
