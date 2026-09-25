/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Basic
public import Mathlib.Data.Set.Lattice.Indexed

/-! # Decision problems induced by function classes

A class of Boolean-valued functions induces a class of predicates through `Decides`.
This construction adds no computation or resource semantics.
-/

@[expose] public section

namespace Complexity

variable {α ι : Type*}

/-- Predicates decided by Boolean-valued functions in the given function class. -/
def DecisionClass (C : Set (α → Bool)) : Set (α → Prop) :=
  {p | ∃ f ∈ C, Decides f p}

namespace DecisionClass

theorem of_decides {C : Set (α → Bool)} {f : α → Bool} {p : α → Prop}
    (hf : f ∈ C) (hp : Decides f p) : p ∈ DecisionClass C :=
  ⟨f, hf, hp⟩

theorem mono {C D : Set (α → Bool)} (h : C ⊆ D) : DecisionClass C ⊆ DecisionClass D :=
  fun _ ⟨f, hf, hp⟩ => ⟨f, h hf, hp⟩

theorem congr {C : Set (α → Bool)} {p q : α → Prop} (hp : p ∈ DecisionClass C)
    (h : ∀ a, p a ↔ q a) : q ∈ DecisionClass C := by
  obtain ⟨f, hf, hp⟩ := hp
  exact ⟨f, hf, hp.congr h⟩

/-- Taking decision predicates commutes with unions of function classes. -/
theorem iUnion (C : ι → Set (α → Bool)) :
    DecisionClass (⋃ i, C i) = ⋃ i, DecisionClass (C i) := by
  ext p
  simp only [DecisionClass, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨f, ⟨i, hf⟩, hp⟩
    exact ⟨i, f, hf, hp⟩
  · rintro ⟨i, f, hf, hp⟩
    exact ⟨f, ⟨i, hf⟩, hp⟩

end DecisionClass

end Complexity
