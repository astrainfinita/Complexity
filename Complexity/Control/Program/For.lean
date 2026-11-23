/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.WP

/-! # Sequencing a statically finite family of programs -/

@[expose] public section

namespace Complexity.Program

variable {F : Type → Type} {O A Op S : Type} {Ret : Op → Type} {k : ℕ}

/-- Execute a fixed finite family in increasing index order, without a dispatch step. -/
def forFin : {k : ℕ} → (Fin k → Program F O A Op Ret Unit) → Program F O A Op Ret Unit
  | 0, _ => pure ()
  | k + 1, f => do
      forFin (fun i : Fin k ↦ f i.castSucc)
      f (Fin.last k)

open Std.WP

variable {m : Type → Type} [Monad m] {Q : MonadQuant m} [MonadLiftT F m] in
/-- The specification of each component suffices to verify the complete finite family. -/
@[spec]
theorem spec_forFin (f : Fin k → Program F O A Op Ret Unit) (e : Semantics O A Op Ret S)
    (I : Invariant ℕ (S → ℕ → Prop))
    (h : ∀ i, Triple ((f i).verifyWith m Q e) (I i.val) (fun _ ↦ I (i.val + 1)) ()) :
    Triple ((forFin f).verifyWith m Q e) (I 0) (fun _ ↦ I k) () := by
  induction k with
  | zero => exact spec_pure () e (fun _ ↦ I 0) ()
  | succ k ih =>
    exact spec_bind_of_spec (ih (fun i ↦ f i.castSucc) (fun i ↦ h i.castSucc))
      (fun _ ↦ h (Fin.last k))

end Complexity.Program
