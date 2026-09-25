/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine
public import Complexity.Models.TreeMachine.Composition

/-! # Composition of encoded tree computations

The intermediate code need not be unique. Its size is bounded by the first
machine's initial mass and time cost, so a monotone time bound for the second
machine gives a bound in terms of the original input size.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β γ : Type*} [Encoding Tree α] [Encoding Tree β] [Encoding Tree γ]
  {k l : ℕ} [NeZero k] [NeZero l] {Q Q' : Type*}

/-- Time cost for composition: a fixed clearing pass and the second computation
on an intermediate code bounded by the first computation's time budget. -/
def compTimeBound (k l : ℕ) (t u : ℕ → ℕ) (n : ℕ) : ℕ :=
  t n + max k l + u (n + k + t n)

/-- Compose finite computations on all valid codes, allowing any valid
intermediate representation of the computed value. -/
theorem Computes.comp {M : TreeMachine Id k Q} {N : TreeMachine Id l Q'}
    {f : α → β} {g : β → γ}
    {t s u v : ℕ → ℕ} (hg : Computes N g u v) (hf : Computes M f t s)
    (hu : Monotone u) :
    Computes (M.comp N) (g ∘ f)
      (compTimeBound k l t u)
      (fun n => n + (max k l + 1) + compTimeBound k l t u n) := by
  intro a x ha
  obtain ⟨b, hb, hm⟩ := hf a x ha
  obtain ⟨c, hc, hn⟩ := hg b (f x) hb
  have hb' := hm.output_size_le
  have ht : t a.size + max k l + u b.size ≤ compTimeBound k l t u a.size := by
    have := hu hb'
    unfold compTimeBound
    omega
  have hcomp := comp_computesInTimeAndSpace M N hm hn
  exact ⟨c, hc, hcomp.space_of_time.mono ht (Nat.add_le_add_left ht _)⟩

end Complexity.TreeMachine
