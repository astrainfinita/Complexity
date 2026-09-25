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

variable {O A Op α S T : Type} {Ret : Op → Type}
  {e : Semantics O A Op Ret S} {e' : Semantics O A Op Ret T}

/-- Relations preserving observations and actions transport complete source executions. -/
theorem Syntax.Exec.simulate (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {v : Kind} {p : Syntax O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (u : T) (hu : R s u) (he : e'.eval = e.eval) :
    ∃ w, R t w ∧ Syntax.Exec e' p u n a w := by
  induction h generalizing u with
  | ret a s => exact ⟨u, hu, .ret a u⟩
  | step o k s h ih =>
    have hv := ho s u hu
    obtain ⟨w, hw, hr⟩ := ih (e'.act (e.eval o (e.observe s)).1 u) (ha _ s u hu)
    exact ⟨w, hw, .step o k u (by simpa only [he, hv] using hr)⟩
  | loop_done a i body k hb hk ihb ihk =>
    obtain ⟨v, hv, hb⟩ := ihb (e'.act a u) (ha a _ u hu)
    obtain ⟨w, hw, hk⟩ := ihk v hv
    exact ⟨w, hw, .loop_done a i body k hb hk⟩
  | loop_next a i body k hb hk ihb ihk =>
    obtain ⟨v, hv, hb⟩ := ihb (e'.act a u) (ha a _ u hu)
    obtain ⟨w, hw, hk⟩ := ihk v hv
    exact ⟨w, hw, .loop_next a i body k hb hk⟩
  | call b k hb hk ih =>
    obtain ⟨v, hv, hb⟩ := Control.Run.simulate R ho ha hb u hu
    obtain ⟨w, hw, hk⟩ := ih v hv
    exact ⟨w, hw, .call b k hb hk⟩

/-- The complete source execution respects a semantic-state projection. -/
theorem Syntax.Exec.map (f : S → T) (ho : ∀ s, e'.observe (f s) = e.observe s)
    (ha : ∀ a s, e'.act a (f s) = f (e.act a s))
    {v : Kind} {p : Syntax O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (he : e'.eval = e.eval) :
    Syntax.Exec e' p (f s) n a (f t) := by
  obtain ⟨w, rfl, hr⟩ := h.simulate (fun s t ↦ t = f s)
    (by rintro s _ rfl; exact ho s) (by rintro a s _ rfl; exact ha a s) (f s) rfl he
  exact hr

/-- The complete source execution can carry additional ghost information. -/
theorem Syntax.Exec.lift (f : T → S) (ho : ∀ s, e'.observe s = e.observe (f s))
    (ha : ∀ a s, f (e'.act a s) = e.act a (f s))
    {v : Kind} {p : Syntax O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (u : T) (hu : f u = s) (he : e'.eval = e.eval) :
    ∃ w, f w = t ∧ Syntax.Exec e' p u n a w :=
  h.simulate (fun s t ↦ f t = s)
    (by rintro _ t rfl; exact ho t) (by rintro a _ t rfl; exact ha a t) u hu he

/-- Transport an entry-to-exit execution along an observation- and action-preserving relation. -/
theorem Exec.simulate (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {p : Program O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (u : T) (hu : R s u) (he : e'.eval = e.eval := by rfl) :
    ∃ w, R t w ∧ p.Exec e' u n a w := Syntax.Exec.simulate R ho ha h u hu he

/-- The same program execution is preserved under a semantic-state projection. -/
theorem Exec.map (f : S → T) (ho : ∀ s, e'.observe (f s) = e.observe s)
    (ha : ∀ a s, e'.act a (f s) = f (e.act a s))
    {p : Program O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (he : e'.eval = e.eval := by rfl) : p.Exec e' (f s) n a (f t) :=
  Syntax.Exec.map f ho ha h he

/-- Lift an entry-to-exit execution through a semantic-state projection. -/
theorem Exec.lift (f : T → S) (ho : ∀ s, e'.observe s = e.observe (f s))
    (ha : ∀ a s, f (e'.act a s) = e.act a (f s))
    {p : Program O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (u : T) (hu : f u = s) (he : e'.eval = e.eval := by rfl) :
    ∃ w, f w = t ∧ p.Exec e' u n a w := Syntax.Exec.lift f ho ha h u hu he

end Complexity.Program
