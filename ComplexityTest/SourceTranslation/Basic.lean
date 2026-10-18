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
  {f : α → β} {g : β → γ} {t p : α → ℕ} {u q : β → ℕ}

-- Composition states its growth across unrelated source universes.
example (hf : Implementation f t p) (hg : Implementation g u q) :
    Implementation (g ∘ f) (fun x => t x + u (f x)) (fun x => max (p x) (q (f x))) :=
  hf.comp hg

-- Input and output identities add no cost.
example (hf : Implementation f t p) :
    Implementation (id ∘ (f ∘ id)) (fun x => 0 + (t x + 0)) (fun x => max 0 (max (p x) 0)) :=
  Implementation.identity.comp (hf.comp Implementation.identity)

-- The same program may be given a weaker growth.
example (hf : Implementation f t p) :
    (hf.mono (t' := fun x => t x + 1) (Dominated.of_le fun _ => Nat.le_succ _)
      (Dominated.refl p)).program = hf.program := rfl

end

-- A concrete composition charges each reversal at its own input.
def reverseTwice {α : Type*} [UniqueEncoding Tree α] :
    Implementation ((List.reverse : List α → List α) ∘ List.reverse)
      (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) :=
  Implementation.reverse.comp Implementation.reverse

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation ((List.reverse : List α → List α) ∘ List.reverse)
      (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  reverseTwice.mono (Dominated.of_le_mul 2 fun xs => by simp; omega)
    (Dominated.of_le fun xs => by simp)

section BranchTranslation

-- Equal field paths must not identify different callback implementations or growths.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g : α → β} {t p u q : α → ℕ} (hf : Implementation f t p) (hg : Implementation g u q) :
    Implementation (fun x : Bool × α => match x.1 with | false => f x.2 | true => g x.2)
      (fun x => if x.1 then u x.2 + 1 else t x.2 + 1)
      (fun x => max ⌜x⌝ₜ.size (if x.1 then q x.2 else p x.2)) := by
  source_calls
  all_goals
    apply Dominated.of_le_mul 2
    rintro ⟨flag, x⟩
    cases flag <;> simp

-- Nested branches retain their own closed environments and selected callback growths.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g h : α → β} {tf pf tg pg th ph : α → ℕ}
    (hf : Implementation f tf pf) (hg : Implementation g tg pg) (hh : Implementation h th ph) :
    Implementation (fun x : Bool × Bool × α =>
      match x.1 with
      | false => f x.2.2
      | true => match x.2.1 with | false => g x.2.2 | true => h x.2.2)
      (fun x => if x.1 then (if x.2.1 then th x.2.2 else tg x.2.2) + 1 else tf x.2.2 + 1)
      (fun x => max ⌜x⌝ₜ.size
        (if x.1 then (if x.2.1 then ph x.2.2 else pg x.2.2) else pf x.2.2)) := by
  source_calls
  all_goals
    apply Dominated.of_le_mul 2
    rintro ⟨outer, inner, x⟩
    cases outer <;> cases inner <;> simp <;> omega

-- Runtime dependent indices are packed; a static parameter need not itself be encodable.
example {α : Type*} (tag : α) {f g : α → (Σ n, Fin n) → Bool} {t p u q : (Σ n, Fin n) → ℕ}
    (hf : Implementation (f tag) t p) (hg : Implementation (g tag) u q) :
    Implementation (fun x : Σ n, Bool × Fin n =>
      match x.2.1 with
      | false => f tag ⟨x.1, x.2.2⟩
      | true => g tag ⟨x.1, x.2.2⟩)
      (fun x => if x.2.1 then u ⟨x.1, x.2.2⟩ + 1 else t ⟨x.1, x.2.2⟩ + 1)
      (fun x => max ⌜x⌝ₜ.size (if x.2.1 then q ⟨x.1, x.2.2⟩ else p ⟨x.1, x.2.2⟩)) := by
  source_calls
  all_goals
    apply Dominated.of_le_mul 2
    rintro ⟨n, flag, i⟩
    cases flag <;> simp

-- Case splitting must not turn pointwise implementations into one uniform program.
example (f : ℕ → Bool → Bool) (t p : ℕ → Bool → ℕ) (_hf : ∀ n, Implementation (f n) (t n) (p n)) :
    True := by
  fail_if_success
    have : Implementation (fun x : Bool × ℕ × Bool =>
      match x.1 with | false => x.2.2 | true => f x.2.1 x.2.2) (fun _ => 1) (fun _ => 1) := by
      source_calls
  trivial

end BranchTranslation

end ComplexityTest.SourceTranslation.Basic
