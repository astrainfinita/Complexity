/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Semantics

/-! # Changing the semantic state of a finite program -/

@[expose] public section

namespace Complexity.Program

variable {F : Type → Type} {O A Op α S T : Type} {Ret : Op → Type}
  {e : Semantics O A Op Ret S} {e' : Semantics O A Op Ret T}

/-- Relations preserving observations and actions transport executions within a budget. -/
theorem Syntax.ExecWithinWith.simulate {m : Type → Type} [Monad m] [MonadLiftT F m]
    {Q : MonadQuant m} (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {v : Kind} {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ} {P : Kind.Value α v → S → ℕ → Prop}
    (h : p.ExecWithinWith m Q e s b P) (u : T) (hu : R s u) (he : e'.eval = e.eval) :
    p.ExecWithinWith m Q e' u b (fun a t' b' ↦ ∃ t, R t t' ∧ P a t b') := by
  induction h generalizing u with
  | ret a s b h => exact .ret a u b ⟨s, hu, h⟩
  | step o k s b _ ih =>
    refine .step o k u b ?_
    rw [he, ho s u hu]
    exact ih _ (ha _ s u hu)
  | choiceOn x k s b P hP _ ih => exact .choiceOn x k u b P hP fun r hr ↦ ih r hr _ (ha r.1 s u hu)
  | «loop» a i body k s b _ _ _ ihb ihn ihd =>
    exact .loop a i body k u b (ihb _ (ha a s u hu)) (fun j t' b' ⟨t, ht, h⟩ ↦ ihn j t b' h t' ht)
      fun j t' b' ⟨t, ht, h⟩ ↦ ihd j t b' h t' ht
  | callOn blk k s b P hb _ ih =>
    exact .callOn blk k u b _ (hb.simulate R ho ha u hu) fun j t' b' ⟨t, ht, h⟩ ↦ ih j t b' h t' ht

end Complexity.Program
