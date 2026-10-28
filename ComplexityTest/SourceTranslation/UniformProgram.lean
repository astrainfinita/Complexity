/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.UniformProgram

-- Library functions with one program at every type are used at types depending on the input.
example : HasProgram (fun x : Σ n, List (Fin n) => x.2.reverse) hole(⊢ program)
    (fun x => 1 + ⌜x.2⌝ₜ.size) (fun x => max ⌜x⌝ₜ.size ⌜x.2⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example := (by source_fun_prop : HasProgram (fun x : Σ n, List (Fin n) => x.2.tail.length) _ _ _)

-- Functions of several arguments are applied to the tuple of their arguments.
example := (by source_fun_prop :
  HasProgram (fun x : Σ n, List (Fin n) × List (Fin n) => x.2.1 ++ x.2.2) _ _ _)

example := (by source_fun_prop : HasProgram (fun x : Σ n, List (Fin n) × ℕ => x.2.1[x.2.2]?) _ _ _)

-- The composition for a family of arguments follows from the fact at every type.
example {α : Type} {β : α → Type} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
    {f g : (x : α) → List (β x)} {pf pg : Value → Code Value} {t p u q : α → ℕ}
    (hf : HasProgram f pf t p) (hg : HasProgram g pg u q) :=
  (by source_fun_prop : HasProgram (fun x => f x ++ g x)
    (fun v => (do let w ← pf v; let z ← pg v; Value.pair w z) >>=
      fun v => do let w ← Value.left v; let z ← Value.right v; List.Code.append w z) _ _)

-- A user's polymorphic function is implemented once, at every type, in the ordinary way: a hole
-- without context is one program at every type.
def swapPair {α β : Type*} (x : α × β) : β × α := (x.2, x.1)

@[fun_prop]
theorem hasProgram_swapPair {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    HasProgram (swapPair : α × β → β × α) hole(⊢ program) (fun _ => 1)
      (fun x => max ⌜x⌝ₜ.size ⌜swapPair x⌝ₜ.size) := by
  abstract_hole program using programSwapPair
  fill_hole program in source_fun_prop

-- Its uses at types depending on the input need no rule for it.
example := (by source_fun_prop :
  HasProgram (fun x : Σ n, Fin n × List (Fin n) => (swapPair x.2).1.reverse) _ _ _)

-- A program that depends on a parameter is not one program at every value of it.
/--
error: Type mismatch
  h
has type
  HasProgram List.reverse program t p
but is expected to have type
  HasProgram List.reverse hole(⊢ uniform) t p
-/
#guard_msgs in
theorem hasProgram_reverseOf {α : Type*} [UniqueEncoding Tree α] {program : Value → Code Value}
    {t p : List α → ℕ} (h : HasProgram (List.reverse : List α → List α) program t p) :
    HasProgram (List.reverse : List α → List α) hole(⊢ uniform) t p := by
  fill_hole uniform in exact h

end ComplexityTest.SourceTranslation.UniformProgram
