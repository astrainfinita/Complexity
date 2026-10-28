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
  {f : α → β} {g : β → γ} {pf pg : Value → Code Value} {t p : α → ℕ} {u q : β → ℕ}

-- Composition states its program and growth across unrelated source universes.
example (hf : HasProgram f pf t p) (hg : HasProgram g pg u q) :
    HasProgram (g ∘ f) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) :=
  hf.comp hg

-- Input and output identities add no cost.
example (hf : HasProgram f pf t p) :
    HasProgram (id ∘ (f ∘ id)) hole(pf ⊢ program) (fun x => 0 + (t x + 0))
      (fun x => max 0 (max (p x) 0)) := by
  fill_hole program in exact HasProgram.identity.comp (hf.comp HasProgram.identity)

-- The same program may be given a weaker growth.
example (hf : HasProgram f pf t p) : HasProgram f pf (fun x => t x + 1) p :=
  hf.mono (Dominated.of_le fun _ => Nat.le_succ _) (Dominated.refl p)

end

-- A concrete composition charges each reversal at its own input.
theorem hasProgram_reverseTwice {α : Type*} [UniqueEncoding Tree α] :
    HasProgram ((List.reverse : List α → List α) ∘ List.reverse) hole(⊢ program)
      (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  abstract_hole program using programReverseTwice
  fill_hole program in
    exact List.hasProgram_reverse.comp List.hasProgram_reverse

example {α : Type*} [UniqueEncoding Tree α] :
    HasProgram ((List.reverse : List α → List α) ∘ List.reverse) programReverseTwice
      (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  hasProgram_reverseTwice.mono (Dominated.of_le_mul 2 fun xs => by simp; omega)
    (Dominated.of_le fun xs => by simp)

section BranchTranslation

-- Equal field paths must not identify different callback implementations or growths.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g : α → β} {pf pg : Value → Code Value} {t p u q : α → ℕ} (hf : HasProgram f pf t p)
    (hg : HasProgram g pg u q) :
    HasProgram (fun x : Bool × α => match x.1 with | false => f x.2 | true => g x.2)
      hole(pf, pg ⊢ program) (fun x => if x.1 then u x.2 + 1 else t x.2 + 1)
      (fun x => max ⌜x⌝ₜ.size (if x.1 then q x.2 else p x.2)) := by
  fill_hole program in source_fun_prop
  all_goals dominated

-- Nested branches retain their own closed environments and selected callback growths.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g h : α → β} {qf qg qh : Value → Code Value} {tf pf tg pg th ph : α → ℕ}
    (hf : HasProgram f qf tf pf) (hg : HasProgram g qg tg pg) (hh : HasProgram h qh th ph) :
    HasProgram (fun x : Bool × Bool × α =>
      match x.1 with
      | false => f x.2.2
      | true => match x.2.1 with | false => g x.2.2 | true => h x.2.2) hole(qf, qg, qh ⊢ program)
      (fun x => if x.1 then (if x.2.1 then th x.2.2 else tg x.2.2) + 1 else tf x.2.2 + 1)
      (fun x => max ⌜x⌝ₜ.size
        (if x.1 then (if x.2.1 then ph x.2.2 else pg x.2.2) else pf x.2.2)) := by
  fill_hole program in source_fun_prop
  all_goals dominated

-- Runtime dependent indices are packed; a static parameter need not itself be encodable.
example {α : Type*} (tag : α) {f g : α → (Σ n, Fin n) → Bool} {pf pg : Value → Code Value}
    {t p u q : (Σ n, Fin n) → ℕ} (hf : HasProgram (f tag) pf t p) (hg : HasProgram (g tag) pg u q) :
    HasProgram (fun x : Σ n, Bool × Fin n =>
      match x.2.1 with
      | false => f tag ⟨x.1, x.2.2⟩
      | true => g tag ⟨x.1, x.2.2⟩) hole(pf, pg ⊢ program)
      (fun x => if x.2.1 then u ⟨x.1, x.2.2⟩ + 1 else t ⟨x.1, x.2.2⟩ + 1)
      (fun x => max ⌜x⌝ₜ.size (if x.2.1 then q ⟨x.1, x.2.2⟩ else p ⟨x.1, x.2.2⟩)) := by
  fill_hole program in source_fun_prop
  all_goals dominated

-- Case splitting must not turn pointwise implementations into one uniform program.
example (f : ℕ → Bool → Bool) (q : ℕ → Value → Code Value) (t p : ℕ → Bool → ℕ)
    (_hf : ∀ n, HasProgram (f n) (q n) (t n) (p n)) :
    True := by
  fail_if_success
    have := (by source_fun_prop : HasProgram (fun x : Bool × ℕ × Bool =>
      match x.1 with | false => x.2.2 | true => f x.2.1 x.2.2) _ (fun _ => 1) (fun _ => 1))
  trivial

end BranchTranslation

end ComplexityTest.SourceTranslation.Basic
