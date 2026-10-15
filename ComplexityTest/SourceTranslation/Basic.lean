/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Translation

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

-- Equal field paths must not identify different callback implementations or budgets.
theorem sameLayoutCallbacks {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g : α → β} (hf : Implementation f) (hg : Implementation g) :
    ∃ impl : Implementation (fun x : Bool × α =>
      match x.1 with | false => f x.2 | true => g x.2),
      ∀ x, impl.bounds.time x = (if x.1 then hg.bounds.time x.2 else hf.bounds.time x.2) + 5 := by
  refine ⟨by source_calls, ?_⟩
  rintro ⟨flag, x⟩
  cases flag <;> simp

-- Nested branches retain their own closed environments and selected callback costs.
theorem nestedCallbackBudgets {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g h : α → β}
    (hf : Implementation f) (hg : Implementation g) (hh : Implementation h) :
    ∃ impl : Implementation (fun x : Bool × Bool × α =>
      match x.1 with
      | false => f x.2.2
      | true => match x.2.1 with | false => g x.2.2 | true => h x.2.2),
      ∀ x, impl.bounds.time x = if x.1 then
        (if x.2.1 then hh.bounds.time x.2.2 else hg.bounds.time x.2.2) + 9
        else hf.bounds.time x.2.2 + 13 := by
  refine ⟨by source_calls, ?_⟩
  rintro ⟨outer, inner, x⟩
  cases outer <;> cases inner <;> simp <;> omega

-- Runtime dependent indices are packed; a static parameter need not itself be encodable.
example {α : Type*} (tag : α) {f g : α → (Σ n, Fin n) → Bool}
    (hf : Implementation (f tag)) (hg : Implementation (g tag)) :
    Implementation (fun x : Σ n, Bool × Fin n =>
      match x.2.1 with
      | false => f tag ⟨x.1, x.2.2⟩
      | true => g tag ⟨x.1, x.2.2⟩) := by source_calls

-- Case splitting must not turn pointwise implementations into one uniform program.
example (f : ℕ → Bool → Bool) (_hf : ∀ n, Implementation (f n)) : True := by
  fail_if_success
    have : Implementation (fun x : Bool × ℕ × Bool =>
      match x.1 with | false => x.2.2 | true => f x.2.1 x.2.2) := by source_calls
  trivial

end BranchTranslation

end ComplexityTest.SourceTranslation.Basic
