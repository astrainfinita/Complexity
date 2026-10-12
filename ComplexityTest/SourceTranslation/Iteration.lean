/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Iteration

-- The loop's program is executable data, without choosing an existential witness.
/-- info: 41 -/
#guard_msgs in
#eval (Implementation.boolNot.iterate.program Value.input).build 1 |>.2.1

def repeatReverse (x : ℕ × List Bool) := List.reverse^[x.1] x.2
example : ∃ b, Realizes repeatReverse b := ⟨_, by source_fun_prop⟩

def repeatAnd (x : List Unit × Bool × Bool) :=
  (fun a => x.2.1 && a)^[x.1.length] x.2.2
example : ∃ b, Realizes repeatAnd b := ⟨_, by source_fun_prop⟩

-- The legacy conclusion remains a thin proof-composition interface.
theorem fixedBudget (f : Bool → Bool) (b : Bounds Bool) (hf : Realizes f b) :
    Realizes (fun x : ℕ × Bool => f^[x.1] x.2) (iterateBounds f b) := hf.iterate

-- Translation uses the selected callback, including for a fixed budget request.
example (f : Bool → Bool) (hf : Implementation f) :
    let selected : Implementation (fun x : ℕ × Bool => f^[x.1] x.2) := by source_fun_prop
    selected.program = hf.iterate.program := rfl

example (f : Bool → Bool) (hf : Implementation f) :
    Realizes (fun x : ℕ × Bool => f^[x.1] x.2) (iterateBounds f hf.bounds) := by
  source_fun_prop

example (f : Bool → Bool) (_hf : Implementation f) : True := by
  fail_if_success
    have : Realizes (fun x : ℕ × Bool => f^[x.1] x.2) ⟨fun _ => 0, fun _ => 0⟩ := by
      source_fun_prop
  trivial

-- Native fun_prop has no source-driver certificate adapter; its existing rules still work.
example (f : Bool → Bool) (b : Bounds Bool) (hf : Realizes f b) :
    ∃ c, Realizes (fun x : ℕ × Bool => f^[x.1] x.2) c := ⟨_, by fun_prop⟩

example (f : Bool → Bool) (b₁ b₂ : Bounds Bool)
    (h₁ : Realizes f b₁) (_h₂ : Realizes f b₂) :
    Realizes (fun x : ℕ × Bool => f^[x.1] x.2) (iterateBounds f b₁) := by
  fun_prop

section Captured

variable (f : Bool → Bool → Bool) (count : Bool → ℕ) (initial : Bool → Bool)
  (bi₁ bi₂ : Bounds Bool) (bs₁ bs₂ : Bounds (Bool × Bool))

theorem capturedFixedBudget
    (hi : Realizes (fun e => (count e, (e, initial e))) bi₁)
    (hs : Realizes (fun x : Bool × Bool => f x.1 x.2) bs₁) :
    Realizes (fun e => (f e)^[count e] (initial e))
      (iterateWithBounds f count initial bi₁ bs₁) := hi.iterateWith hs

example (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : Bool × Bool => f x.1 x.2)) :
    let selected : Implementation (fun e => (f e)^[count e] (initial e)) := by source_fun_prop
    selected.program = (hi.iterateWith hs).program := rfl

example (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : Bool × Bool => f x.1 x.2)) :
    Realizes (fun e => (f e)^[count e] (initial e))
      (iterateWithBounds f count initial hi.bounds hs.bounds) := by source_fun_prop

example (_hi : Implementation (fun e => (count e, (e, initial e))))
    (_hs : Implementation (fun x : Bool × Bool => f x.1 x.2)) : True := by
  fail_if_success
    have : Realizes (fun e => (f e)^[count e] (initial e))
        ⟨fun _ => 0, fun _ => 0⟩ := by source_fun_prop
  trivial

-- Native fun_prop still propagates fixed budgets to its existential callback rules.
example
    (hi₁ : Realizes (fun e => (count e, (e, initial e))) bi₁)
    (_hi₂ : Realizes (fun e => (count e, (e, initial e))) bi₂)
    (hs₁ : Realizes (fun x : Bool × Bool => f x.1 x.2) bs₁)
    (_hs₂ : Realizes (fun x : Bool × Bool => f x.1 x.2) bs₂) :
    Realizes (fun e => (f e)^[count e] (initial e))
      (iterateWithBounds f count initial bi₁ bs₁) := by fun_prop

end Captured

-- Native existential search also requires one callback accepting every environment.
example (f : Bool → Bool → Bool)
    (_h : ∀ e, ∃ b, Realizes (f e) b) : True := by
  fail_if_success
    have : ∃ b, Realizes (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) b :=
      ⟨_, by fun_prop⟩
  trivial

-- Even concrete programs for each separate environment are not a uniform callback.
example (f : Bool → Bool → Bool) (_h : ∀ e, Implementation (f e)) : True := by
  fail_if_success
    have : Implementation (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) := by
      source_fun_prop
  trivial

theorem perStepBounds (f : Bool → Bool) (hf : Implementation f) :
    ∃ c, Realizes (fun x : ℕ × Bool => f^[x.1] x.2) c ∧
      ∀ a, c.time (2, a) = hf.bounds.time a + hf.bounds.time (f a) + 2057 ∧
        c.peak (2, a) = max (20 * ⌜((2 : ℕ), a)⌝ₜ.size + 100)
          (max (2 * hf.bounds.peak a) (max (20 * ⌜((1 : ℕ), f a)⌝ₜ.size + 100)
            (max (2 * hf.bounds.peak (f a)) (2 * ⌜((0 : ℕ), f (f a))⌝ₜ.size + 10)))) := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro a
  constructor
  · simp [iterateBounds, show Nat.bits 2 = [false, true] from rfl]
    omega
  · rfl

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
