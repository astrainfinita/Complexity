/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Asymptotics.Polynomial

open Complexity

-- Keep retired program specifications and analysis dependencies out of this API.
open Lean Elab in
run_elab do
  let env ← getEnv
  for name in [`Complexity.IsBigO, `Complexity.UniformBound, `Complexity.DominatedAt,
      `Complexity.Dominated.uniformBound_of_pos] do
    if env.contains name then
      throwError "retired resource interface remains exported: {name}"
  if env.contains `Asymptotics.IsBigO || env.contains `Real then
    throwError "natural resource bounds unexpectedly imported real analysis"

-- A size-bound complexity comparison may ignore the zero-size exception.
example : DominatedAtTop (fun n => if n = 0 then 1000 else n) id :=
  dominatedAtTop_iff.2 ⟨1, 1, fun n hn => by simp [show n ≠ 0 by omega]⟩

-- A program specification must account for the same exception.
example : ¬Dominated (fun n => if n = 0 then 1000 else n) id := by
  rintro ⟨C, h⟩
  simpa using h 0

-- Zero resources stay zero, even on finite input types.
example : Dominated (fun _ : Bool => 0) (fun _ => (0 : ℕ)) := Dominated.zero
example : ¬Dominated (fun _ : Bool => 1) (fun _ => (0 : ℕ)) := by
  rintro ⟨C, h⟩
  simpa using h false

-- Constant calls are valid substitutions and retain the original coefficient.
example {α β : Type*} {f g : α → ℕ} (h : Dominated f g) (a : α) :
    Dominated (fun _ : β => f a) (fun _ => g a) := h.comp (fun _ => a)

-- One specification ranges over all callback arguments, before summation.
example {α : Type*} (n : α → ℕ) (a : (x : α) → Fin (n x) → ℕ) (b : α → ℕ)
    (h : Dominated (fun z : Σ x, Fin (n x) => a z.1 z.2) (fun z => b z.1)) :
    Dominated (fun x => ((List.finRange (n x)).map (a x)).sum) (fun x => n x * b x) :=
  h.sum_finRange

-- Addition alone suffices for general resource values; no multiplication is assumed.
example {α M : Type*} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {f g h : α → M} (hf : Dominated f h) (hg : Dominated g h) :
    Dominated (fun x => f x + g x) h := hf.add_same hg

-- Separate coefficients for infinitely many callbacks cannot masquerade as one family bound.
example : (∀ i : ℕ, Dominated (fun _ : Unit => i) (fun _ => 1)) ∧
    ¬Dominated (fun z : ℕ × Unit => z.1) (fun _ => 1) := by
  refine ⟨fun i => Dominated.const i, ?_⟩
  rintro ⟨C, h⟩
  have := h (C + 1, ())
  simp only [Nat.nsmul_eq_mul, Nat.mul_one] at this
  omega
