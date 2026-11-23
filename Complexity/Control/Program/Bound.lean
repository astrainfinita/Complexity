/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.WP

/-! # Using coarse time bounds for verified subprograms -/

@[expose] public section

namespace Complexity.Program

open Std.WP

variable {F : Type → Type} {O A Op S α : Type} {Ret : Op → Type} {m : Type → Type}
  [Monad m] {Q : MonadQuant m} [MonadLiftT F m]
  {p : Program F O A Op Ret α} {e : Semantics O A Op Ret S}
  {P : S → Prop} {R : α → S → Prop} {n k : ℕ}

/-- A component with an exact cost may be called with any larger budget. -/
theorem spec_exact_budget_le
    (h : ∀ q, Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ b = n + q)
      (fun a s b ↦ R a s ∧ b = q) ()) (hk : n ≤ k) (q : ℕ) :
    Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ k + q ≤ b)
      (fun a s b ↦ R a s ∧ q ≤ b) () := by
  constructor
  rintro s b ⟨hp, hb⟩
  apply (Triple.entails_wp_of_post (h (b - n)) ?_) s b ⟨hp, by omega⟩
  rintro a t c ⟨hq, ht⟩
  exact ⟨hq, by omega⟩

/-- A coarse component bound may be enlarged without consuming the extra credits. -/
theorem spec_budget_le
    (h : ∀ q, Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ n + q ≤ b)
      (fun a s b ↦ R a s ∧ q ≤ b) ()) (hk : n ≤ k) (q : ℕ) :
    Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ k + q ≤ b)
      (fun a s b ↦ R a s ∧ q ≤ b) () := by
  constructor
  rintro s b ⟨hp, hb⟩
  exact (h q).le_wp s b ⟨hp, by omega⟩

end Complexity.Program
