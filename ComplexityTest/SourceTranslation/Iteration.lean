/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Iteration

def repeatReverse (x : ℕ × List Bool) := List.reverse^[x.1] x.2
example : ∃ b, Realizes repeatReverse b := ⟨_, by source_fun_prop⟩

def repeatAnd (x : List Unit × Bool × Bool) :=
  (fun a => x.2.1 && a)^[x.1.length] x.2.2
example : ∃ b, Realizes repeatAnd b := ⟨_, by source_fun_prop⟩

-- Per-environment witnesses cannot stand in for one callback accepting every environment.
example (f : Bool → Bool → Bool)
    (_h : ∀ e, ∃ b, Realizes (f e) b) : True := by
  fail_if_success
    have : ∃ b, Realizes (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) b :=
      ⟨_, by source_fun_prop⟩
  trivial

example (f : Bool → Bool) (b : Bounds Bool) (hf : Realizes f b) :
    ∃ c, Realizes (fun x : ℕ × Bool => f^[x.1] x.2) c ∧
      ∀ a, c.time (2, a) = b.time a + b.time (f a) + 2057 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro a
  simp [iterateBounds, show Nat.bits 2 = [false, true] from rfl]
  omega
def repeatNot (x : List Unit × Bool) := Bool.not^[x.1.length] x.2

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace repeatNot
    (fun n => 10000 * (n + 1) ^ 2) (fun n => k * (1000 * n + 1000)) := by
  model_fun_prop
  all_goals
    rename_i input
    rcases input with ⟨xs, a⟩
    have hl := length_le_codeSize xs
    have hb := size_encode_bool_le a
    have hi := iterateCost_le Bool.not ⟨fun _ => 4, fun _ => 3⟩
      (fun i (_ : Bool) => i ≤ xs.length)
      (fun i _ => (400 * xs.length + 524) * i)
      (100 * xs.length + 300) xs.length a (by rfl)
      (by
        intro i a hi
        have hn := size_encode_nat_le (i + 1)
        have hb := size_encode_bool_le a
        dsimp only
        refine ⟨by omega, ?_, ?_, by omega⟩
        · nlinarith
        · simp only [size_encode_prod]
          omega)
      (by
        intro a _
        have := size_encode_bool_le a
        simp only [size_encode_prod, encode_nat_tree, Nat.zero_bits, encode_list_nil,
          size_encode_unit]
        omega)
    have hn := size_encode_nat_le xs.length
    have hp := pow_le_pow_left' (Nat.add_le_add_right hl 1) 2
    cases a <;> simp only [size_encode_prod, encode_bool_true, encode_bool_false,
      encode_nat_tree, Bool.false_eq_true, ↓reduceIte, size_encode_unit] at hi hn ⊢ <;> nlinarith [hi.2.1, hi.2.2]

end ComplexityTest.SourceTranslation.Iteration
