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

/-- Relations preserving observations and actions transport complete source executions. -/
theorem Syntax.Exec.simulate (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {v : Kind} {p : Syntax Id O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (u : T) (hu : R s u) (he : e'.eval = e.eval) :
    ∃ w, R t w ∧ Syntax.Exec e' p u n a w := by
  obtain ⟨l, a', w, hl, he', t', ht, ha', rfl, hb⟩ :=
    ExecWithin.exists_exec (ExecWithinWith.simulate R ho ha h u hu he)
  obtain rfl : l = n := by omega
  exact ⟨w, ht, ha' ▸ he'⟩

/-- The complete source execution respects a semantic-state projection. -/
theorem Syntax.Exec.map (f : S → T) (ho : ∀ s, e'.observe (f s) = e.observe s)
    (ha : ∀ a s, e'.act a (f s) = f (e.act a s))
    {v : Kind} {p : Syntax Id O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (he : e'.eval = e.eval) :
    Syntax.Exec e' p (f s) n a (f t) := by
  obtain ⟨w, rfl, hr⟩ := h.simulate (fun s t ↦ t = f s)
    (by rintro s _ rfl; exact ho s) (by rintro a s _ rfl; exact ha a s) (f s) rfl he
  exact hr

/-- The complete source execution can carry additional ghost information. -/
theorem Syntax.Exec.lift (f : T → S) (ho : ∀ s, e'.observe s = e.observe (f s))
    (ha : ∀ a s, f (e'.act a s) = e.act a (f s))
    {v : Kind} {p : Syntax Id O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (h : Syntax.Exec e p s n a t) (u : T) (hu : f u = s) (he : e'.eval = e.eval) :
    ∃ w, f w = t ∧ Syntax.Exec e' p u n a w :=
  h.simulate (fun s t ↦ f t = s)
    (by rintro _ t rfl; exact ho t) (by rintro a _ t rfl; exact ha a t) u hu he

/-- Transport an entry-to-exit execution along an observation- and action-preserving relation. -/
theorem Exec.simulate (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {p : Program Id O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (u : T) (hu : R s u) (he : e'.eval = e.eval := by rfl) :
    ∃ w, R t w ∧ p.Exec e' u n a w := Syntax.Exec.simulate R ho ha h u hu he

/-- The same program execution is preserved under a semantic-state projection. -/
theorem Exec.map (f : S → T) (ho : ∀ s, e'.observe (f s) = e.observe s)
    (ha : ∀ a s, e'.act a (f s) = f (e.act a s))
    {p : Program Id O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (he : e'.eval = e.eval := by rfl) : p.Exec e' (f s) n a (f t) :=
  Syntax.Exec.map f ho ha h he

/-- Lift an entry-to-exit execution through a semantic-state projection. -/
theorem Exec.lift (f : T → S) (ho : ∀ s, e'.observe s = e.observe (f s))
    (ha : ∀ a s, f (e'.act a s) = e.act a (f s))
    {p : Program Id O A Op Ret α} {s t : S} {n : ℕ} {a : α} (h : p.Exec e s n a t)
    (u : T) (hu : f u = s) (he : e'.eval = e.eval := by rfl) :
    ∃ w, f w = t ∧ p.Exec e' u n a w := Syntax.Exec.lift f ho ha h u hu he

end Complexity.Program
