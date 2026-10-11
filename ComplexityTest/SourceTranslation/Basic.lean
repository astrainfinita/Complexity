/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Basic

universe u v w

section

variable {α : Type u} {β : Type v} {γ : Type w}
  [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
  {f : α → β} {g : β → γ}

-- Composition and its budget interface work across unrelated source universes.
example (hf : Implementation f) (hg : Implementation g) (x : α) :
    (hf.comp hg).bounds.time x = hf.bounds.time x + hg.bounds.time (f x) := by
  simp

example (hf : Implementation f) (hg : Implementation g) (x : α) :
    (hf.comp hg).bounds.peak x = max (hf.bounds.peak x) (hg.bounds.peak (f x)) := by
  simp

-- Adding input/output identities needs no Writer or universe conversion from the user.
example (hf : Implementation f) (x : α) :
    (Implementation.identity.comp (hf.comp Implementation.identity)).bounds.time x =
      hf.bounds.time x := by
  simp

-- A relaxed budget keeps the exact same implementation, including under composition.
example (hf : Implementation f) (hg : Implementation g) (b : Bounds α)
    (h : ∀ x, hf.bounds.time x ≤ b.time x ∧ hf.bounds.peak x ≤ b.peak x) :
    ((hf.rebudget b h).comp hg).program = (hf.comp hg).program := rfl

example (hf : Implementation f) (b : Bounds α)
    (h : ∀ x, hf.bounds.time x ≤ b.time x ∧ hf.bounds.peak x ≤ b.peak x) :
    Realizes f b := by
  simpa using (hf.rebudget b h).realizes

end

-- A concrete composition exposes ordinary list facts and arithmetic to its consumer.
def reverseTwice {α : Type*} [UniqueEncoding Tree α] :
    Implementation ((List.reverse : List α → List α) ∘ List.reverse) :=
  Implementation.reverse.comp Implementation.reverse

example {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    (reverseTwice.evaluate xs).value = xs := by
  rw [Implementation.value_eq]
  simp

example {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    reverseTwice.bounds.time xs = 26 * xs.length + 16 := by
  simp [reverseTwice]
  omega

section BranchTranslation

attribute [local fun_prop] Realizes.comp Realizes.of_encode
  fst_realizes snd_realizes identity_realizes Realizes.pair encode_realizes

-- Equal field paths must not identify different callback implementations or budgets.
theorem sameLayoutCallbacks {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g : α → β} {bf bg : Bounds α} (hf : Realizes f bf) (hg : Realizes g bg) :
    ∃ b, Realizes (fun x : Bool × α =>
      match x.1 with | false => f x.2 | true => g x.2) b ∧
      ∀ x, b.time x = (if x.1 then bg.time x.2 else bf.time x.2) + 5 := by
  refine ⟨_, by source_calls, ?_⟩
  rintro ⟨flag, x⟩
  cases flag <;> simp

-- Nested branches retain their own closed environments and selected callback costs.
theorem nestedCallbackBudgets {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g h : α → β} {bf bg bh : Bounds α}
    (hf : Realizes f bf) (hg : Realizes g bg) (hh : Realizes h bh) :
    ∃ b, Realizes (fun x : Bool × Bool × α =>
      match x.1 with
      | false => f x.2.2
      | true => match x.2.1 with | false => g x.2.2 | true => h x.2.2) b ∧
      ∀ x, b.time x = if x.1 then
        (if x.2.1 then bh.time x.2.2 else bg.time x.2.2) + 9
        else bf.time x.2.2 + 13 := by
  refine ⟨_, by source_calls, ?_⟩
  rintro ⟨outer, inner, x⟩
  cases outer <;> cases inner <;> simp <;> omega

-- Runtime dependent indices are packed; a static parameter need not itself be encodable.
example {α : Type*} (tag : α) {f g : α → (Σ n, Fin n) → Bool}
    {bf bg : Bounds (Σ n, Fin n)}
    (hf : Realizes (f tag) bf) (hg : Realizes (g tag) bg) :
    ∃ b, Realizes (fun x : Σ n, Bool × Fin n =>
      match x.2.1 with
      | false => f tag ⟨x.1, x.2.2⟩
      | true => g tag ⟨x.1, x.2.2⟩) b := ⟨_, by source_calls⟩

-- Case splitting must not turn pointwise implementations into one uniform program.
example (f : ℕ → Bool → Bool) (b : ℕ → Bounds Bool)
    (_hf : ∀ n, Realizes (f n) (b n)) : True := by
  fail_if_success
    have : ∃ c, Realizes (fun x : Bool × ℕ × Bool =>
      match x.1 with | false => x.2.2 | true => f x.2.1 x.2.2) c :=
      ⟨_, by source_calls⟩
  trivial

-- A failed earlier candidate must release its inferred budget for the next certificate.
example (f : Bool → Bool) (hgood : Realizes f ⟨fun _ => 1, fun _ => 1⟩)
    (_hbad : False → Realizes f identityBounds) :
    ∃ b, Realizes f b ∧ ∀ x, b.time x = 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  rfl

-- The model bridge uses the same search, including its rollback behavior.
example (f : Bool → Bool) (hgood : Realizes f ⟨fun _ => 1, fun _ => 1⟩)
    (_hbad : False → Realizes f identityBounds) :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace f
      (fun _ => 5) (fun n => k * (n + 3)) := by
  model_fun_prop

end BranchTranslation

end ComplexityTest.SourceTranslation.Basic
