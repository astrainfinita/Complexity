/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Basic

/-! # Many-one reductions

A many-one reduction relative to a class of functions `C` maps instances of `p` to instances of `q`
preserving membership. Polynomial-time many-one reductions are the case `C = FP model`. Identity,
composition, and preimage closure of decision classes require the corresponding closure properties
of the underlying function classes.
-/

@[expose] public section

namespace Complexity

/-- `p` many-one reduces to `q` via a function in `C`. In particular,
`ManyOneReducible (FP model) p q` is a polynomial-time many-one reduction. -/
def ManyOneReducible {α β : Type*} (C : Set (α → β)) (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ f ∈ C, ∀ x, p x ↔ q (f x)

namespace ManyOneReducible

variable {α β γ : Type*} {p p' : α → Prop} {q q' : β → Prop} {r : γ → Prop}

theorem mono {C C' : Set (α → β)} (h : ManyOneReducible C p q) (hC : C ⊆ C') :
    ManyOneReducible C' p q :=
  let ⟨f, hf, hiff⟩ := h
  ⟨f, hC hf, hiff⟩

theorem congr {C : Set (α → β)} (h : ManyOneReducible C p q)
    (hp : ∀ x, p x ↔ p' x) (hq : ∀ y, q y ↔ q' y) : ManyOneReducible C p' q' :=
  let ⟨f, hf, hiff⟩ := h
  ⟨f, hf, fun x => (hp x).symm.trans ((hiff x).trans (hq (f x)))⟩

theorem refl {C : Set (α → α)} (hid : id ∈ C) (p : α → Prop) : ManyOneReducible C p p :=
  ⟨id, hid, fun _ => Iff.rfl⟩

theorem trans {C₁ : Set (α → β)} {C₂ : Set (β → γ)} {C₃ : Set (α → γ)}
    (hcomp : ∀ {f g}, g ∈ C₂ → f ∈ C₁ → g ∘ f ∈ C₃)
    (hpq : ManyOneReducible C₁ p q) (hqr : ManyOneReducible C₂ q r) :
    ManyOneReducible C₃ p r :=
  let ⟨f, hf, hp⟩ := hpq
  let ⟨g, hg, hq⟩ := hqr
  ⟨g ∘ f, hcomp hg hf, fun x => (hp x).trans (hq (f x))⟩

/-- A decision class closed under precomposition with `C` is closed downward under `C`-many-one
reductions. -/
theorem mem_decisionClass {C : Set (α → β)} {D : Set (β → Bool)} {E : Set (α → Bool)}
    (hcomp : ∀ {f g}, g ∈ D → f ∈ C → g ∘ f ∈ E)
    (hpq : ManyOneReducible C p q) (hq : q ∈ DecisionClass D) : p ∈ DecisionClass E :=
  let ⟨f, hf, hiff⟩ := hpq
  let ⟨_, hg, hdec⟩ := hq
  DecisionClass.of_decides (hcomp hg hf) ((hdec.comp (f := f)).congr fun x => (hiff x).symm)

end ManyOneReducible

end Complexity
