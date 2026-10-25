/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.UniformProgram

-- Library functions with one program at every type are used at types depending on the input.
example : Implementation (fun x : Σ n, List (Fin n) => x.2.reverse)
    (fun x => 1 + ⌜x.2⌝ₜ.size) (fun x => max (max ⌜x⌝ₜ.size ⌜x.2⌝ₜ.size) ⌜x.2⌝ₜ.size) := by
  source_fun_prop

example := (by source_fun_prop : Implementation (fun x : Σ n, List (Fin n) => x.2.tail.length) _ _)

-- The generated program is the library's program.
example : List.programReverse = List.Code.reverse := rfl

-- A user's polymorphic function is implemented once, at every type, in the ordinary way.
def swapPair {α β : Type*} (x : α × β) : β × α := (x.2, x.1)

@[uniform_program]
def implementationSwapPair {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :=
  (by source_fun_prop : Implementation (swapPair : α × β → β × α) _ _)

example : HasProgram (swapPair : Bool × ℕ → ℕ × Bool) programSwapPair (fun _ => 1 + (1 + 1))
    (fun x => max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size ⌜(x.2, x.1)⌝ₜ.size)) :=
  hasProgram_swapPair

-- Its uses at types depending on the input need no rule for it.
example := (by source_fun_prop :
  Implementation (fun x : Σ n, Fin n × List (Fin n) => (swapPair x.2).1.reverse) _ _)

-- A program that depends on a parameter is not one program at every value of it.
def implementationReverseOf {α : Type*} [UniqueEncoding Tree α] {t p : List α → ℕ}
    (h : Implementation (List.reverse : List α → List α) t p) :
    Implementation (List.reverse : List α → List α) t p := h

/--
error: uniform_program: the program of implementationReverseOf depends on [α, inst✝, t, p, h]
-/
#guard_msgs in
attribute [uniform_program] implementationReverseOf

-- The generated names come from `implementationS`; for other names the stem is given.
def headPairChoice {α : Type*} [UniqueEncoding Tree α] :=
  (by source_fun_prop : Implementation (fun xs : List α => (xs.head?, xs)) _ _)

/--
error: uniform_program: name headPairChoice `N.implementationS`, or give the stem with `uniform_program N.s`
-/
#guard_msgs in
attribute [uniform_program] headPairChoice

attribute [uniform_program headPair] headPairChoice

example := (hasProgram_headPair :
  HasProgram (fun xs : List Bool => (xs.head?, xs)) programHeadPair _ _)

end ComplexityTest.SourceTranslation.UniformProgram
