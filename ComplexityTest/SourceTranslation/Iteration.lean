/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
namespace ComplexityTest.SourceTranslation.Iteration

-- The loop stores executable code and keeps the selected callback.
example (f : Bool → Bool) {qf : Value → Code Value} {t p : Bool → ℕ}
    (hf : HasProgramInO f qf t p) :=
  (by source_fun_prop : type_of% hf.iterate)

-- The growth refers to the chosen callback's growth at each visited state.
example (f : Bool → Bool) {qf : Value → Code Value} {t p : Bool → ℕ}
    (_hf : HasProgramInO f qf t p) :
    HasProgramInO (fun x : ℕ × Bool => f^[x.1] x.2) hole(qf ⊢ program)
      (fun x => iterateTime f t x.1 x.2 + 1) (fun x => iteratePeak f p x.1 x.2) := by
  fill_hole program in source_fun_prop

def repeatReverse (x : ℕ × List Bool) := List.reverse^[x.1] x.2
example := (by source_fun_prop : HasProgramInO repeatReverse _ _ _)

def repeatAnd (x : List Unit × Bool × Bool) :=
  (fun a => x.2.1 && a)^[x.1.length] x.2.2
example := (by source_fun_prop : HasProgramInO repeatAnd _ _ _)

def repeatNot (x : List Unit × Bool) := Bool.not^[x.1.length] x.2
example := (by source_fun_prop : HasProgramInO repeatNot _ _ _)

section Captured

variable (f : Bool → Bool → Bool) (count : Bool → ℕ) (initial : Bool → Bool)

example {qi qs : Value → Code Value} {ti pi : Bool → ℕ} {ts ps : Bool × Bool → ℕ}
    (hi : HasProgramInO (fun e => (count e, (e, initial e))) qi ti pi)
    (hs : HasProgramInO (fun x : Bool × Bool => f x.1 x.2) qs ts ps) :=
  (by source_fun_prop : type_of% (hi.iterate_with hs))

end Captured

-- Separate implementations for each environment are not a uniform callback.
example (f : Bool → Bool → Bool) (program : Bool → Value → Code Value)
    (_h : ∀ e, HasProgramInO (f e) (program e) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgramInO (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) _ _ _)
  trivial

-- Two iterations pay both state-dependent callbacks once, and each binary counter step.
example (f : Bool → Bool) (t : Bool → ℕ) (a : Bool) :
    iterateTime f t 2 a = t a + t (f a) + ⌜(2 : ℕ)⌝ₜ.size + ⌜(1 : ℕ)⌝ₜ.size := by
  simp only [iterateTime_succ, iterateTime_zero, Nat.reduceAdd]
  omega

-- A varying round allowance retains the sum of the two visited callback growths.
-- The proof uses a potential and the source invariant.
example {α : Type*} [UniqueEncoding Tree α] {f : α → α} {t p : α → ℕ} :
    Dominated (fun x => iterateTime f t 2 x) (fun x => t x + t (f x) + 1) := by
  let I (x : α) (n : ℕ) (a : α) :=
    (n = 2 ∧ a = x) ∨ (n = 1 ∧ a = f x) ∨ (n = 0 ∧ a = f (f x))
  let remaining (_ : α) (n : ℕ) (a : α) :=
    if n = 0 then 0 else if n = 1 then t a + ⌜(1 : ℕ)⌝ₜ.size
    else (t a + ⌜(2 : ℕ)⌝ₜ.size) + (t (f a) + ⌜(1 : ℕ)⌝ₜ.size)
  let peak (x : α) :=
    max (max ⌜((2 : ℕ), x)⌝ₜ.size
      (max ⌜((1 : ℕ), f x)⌝ₜ.size ⌜((0 : ℕ), f (f x))⌝ₜ.size))
      (max (p x) (p (f x)))
  have bounds := Dominated.iterate_of_potential (f := fun _ => f) (t := fun _ => t)
    (p := fun _ => p) I (fun _ => 2) id
    remaining peak (fun _ => Or.inl ⟨rfl, rfl⟩) (fun x n a hi => by
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
      · omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · have : n = 1 := by omega
        subst n
        simp [remaining]
      · have : n = 0 := by omega
        subst n
        simp [remaining]
      · omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp [peak] <;> omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · dsimp [peak]
        omega
      · dsimp [peak]
        omega
      · omega)
  apply bounds.1.trans
  apply (((Dominated.refl t).add (Dominated.refl (fun x => t (f x)))).add
    (Dominated.const (⌜(2 : ℕ)⌝ₜ.size + ⌜(1 : ℕ)⌝ₜ.size))).mono_left
  intro x
  norm_num only [remaining, id_eq]
  simp only [ite_false]
  omega

-- Zero captured iterations charge preparation once; no callback growth remains.
example {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {initial : ρ → α} {qi qs : Value → Code Value} {ti pi : ρ → ℕ}
    {t p : ρ × α → ℕ} (hi : HasProgramInO (fun e => ((0 : ℕ), (e, initial e))) qi ti pi)
    (hs : HasProgramInO (fun x : ρ × α => f x.1 x.2) qs t p) :
    HasProgramInO (fun e => (f e)^[0] (initial e)) hole(qi, qs ⊢ program) (fun e => ti e + 1)
      (fun e => max (pi e) (⌜e⌝ₜ.size + 1 + ⌜((0 : ℕ), initial e)⌝ₜ.size)) := by
  fill_hole program in
    exact (hi.iterate_with hs).mono (Dominated.of_le fun _ => by simp)
      (Dominated.of_le fun _ => by simp)

section IterateGrowth

-- The growth of an iteration whose count is the length of a list is settled without the user: a
-- polynomial time and peak. Guards the rules `IsPoly.iterateTime` and `IsPoly.iteratePeak`
-- registered with `@[dominated_traversal]`; if this needs a `dominated` line again, they are no
-- longer applied.
example : HasProgramIn repeatNot hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size)
    (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- The peak is linear: the states, the stored counters and the callback are. Guards
-- `Dominated.iteratePeak_of_reached`. The same with a callback reading a captured flag.
example : HasProgramIn repeatNot hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size)
    IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

example : HasProgramIn repeatAnd hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size)
    IsO(fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private theorem size_cons_iterate_le (k : ℕ) (l : List Bool) :
    ⌜(List.cons true)^[k] l⌝ₜ.size ≤ ⌜l⌝ₜ.size + 4 * k := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    have := ih (true :: l)
    have := size_encode_bool_le true
    simp only [Function.iterate_succ_apply, encode_list_cons, size_encode_prod] at *
    omega

-- A state that grows needs a bound on the states reached within the count: the user gives it as
-- a lemma about the iteration of any count, and the rules do the rest.
example : HasProgramIn (fun x : List Unit × List Bool => (List.cons true)^[x.1.length] x.2)
    hole(⊢ program) (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated [size_cons_iterate_le]

private theorem size_reverse_iterate (k : ℕ) (l : List Bool) :
    ⌜List.reverse^[k] l⌝ₜ.size = ⌜l⌝ₜ.size := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, size_encode_reverse]

-- The count is a number: `x.1` rounds can be exponential in the code, so no growth in the code
-- alone bounds them. In a measure that counts the number itself, the count premise holds and the
-- rules settle the rest, with the size of the states given.
example : HasProgramIn repeatReverse hole(⊢ program) (IsPoly fun x => x.1 + ⌜x⌝ₜ.size)
    (IsPoly fun x => x.1 + ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  all_goals dominated [size_reverse_iterate]

end IterateGrowth

end ComplexityTest.SourceTranslation.Iteration
