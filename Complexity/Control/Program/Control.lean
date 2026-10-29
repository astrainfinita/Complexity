/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Nat.Notation

/-! # Controllers with internal states and exits -/

@[expose] public section

namespace Complexity.Program

/-- A controller with separate internal states and exits. -/
structure Control (O A Q E : Type) where
  /-- The initial internal state or immediate exit. -/
  start : Q ⊕ E
  /-- One local action and the next internal state or exit. -/
  next : Q → O → A × (Q ⊕ E)

namespace Control

variable {O A Q E Q' E' S α β : Type}

/-- Exact execution of a controller, with one unit charged per transition. -/
inductive Run (c : Control O A Q E) (out : E → α)
    (observe : S → O) (act : A → S → S) : Q ⊕ E → S → ℕ → α → S → Prop where
  | done (e : E) (s : S) : Run c out observe act (.inr e) s 0 (out e) s
  | step (q : Q) (s : S) {n : ℕ} {a : α} {t : S}
      (h : Run c out observe act (c.next q (observe s)).2
        (act (c.next q (observe s)).1 s) n a t) :
      Run c out observe act (.inl q) s (n + 1) a t

/-- Embed a controller and attach computations at its exits without charging a step. -/
theorem Run.link {c : Control O A Q E} {d : Control O A Q' E'}
    {out : E → α} {out' : E' → β} {observe : S → O} {act : A → S → S}
    (f : Q → Q') (g : E → Q' ⊕ E')
    (hn : ∀ q o, d.next (f q) o =
      ((c.next q o).1, Sum.elim (fun q ↦ Sum.inl (f q)) g (c.next q o).2))
    {q : Q ⊕ E} {s t u : S} {n m : ℕ} {a : α} {b : β}
    (h : Run c out observe act q s n a t)
    (he : ∀ e, out e = a → Run d out' observe act (g e) t m b u) :
    Run d out' observe act (Sum.elim (fun q ↦ Sum.inl (f q)) g q) s (n + m) b u := by
  induction h with
  | done e s => simpa using he e rfl
  | step q s h ih =>
      have hh := Run.step (c := d) (f q) s
        (by simpa only [hn, Prod.fst, Prod.snd] using ih he)
      simpa only [Sum.elim_inl, Nat.add_right_comm] using hh

/-- Relabel a controller while preserving its actions and returned values. -/
theorem Run.relabel {c : Control O A Q E} {d : Control O A Q' E'}
    {out : E → α} {out' : E' → α} {observe : S → O} {act : A → S → S}
    (f : Q → Q') (g : E → E')
    (hn : ∀ q o, d.next (f q) o = ((c.next q o).1, Sum.map f g (c.next q o).2))
    (he : ∀ e, out' (g e) = out e)
    {q : Q ⊕ E} {s t : S} {n : ℕ} {a : α}
    (h : Run c out observe act q s n a t) :
    Run d out' observe act (Sum.map f g q) s n a t := by
  have hh := h.link f (Sum.inr ∘ g) (by
    intro q o
    rw [hn]
    cases (c.next q o).2 <;> rfl) (by
      intro e ha
      simpa only [Function.comp_apply, he, ha] using
        Run.done (out := out') (g e) t)
  cases q <;> simpa only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, Nat.add_zero] using hh

/-- Execution depends on the transition function, not the controller's entry label. -/
theorem Run.congr_next {c d : Control O A Q E}
    {out : E → α} {observe : S → O} {act : A → S → S}
    {q : Q ⊕ E} {s t : S} {n : ℕ} {a : α}
    (h : Run c out observe act q s n a t) (hn : c.next = d.next) :
    Run d out observe act q s n a t := by
  simpa only [Sum.map_id_id, id_eq] using h.relabel id id
    (by intro q o; rw [← hn]; simp only [id_eq, Sum.map_id_id]) (fun _ ↦ rfl)

variable {T : Type} {c : Control O A Q E} {out : E → α}
  {o : S → O} {act : A → S → S} {o' : T → O} {act' : A → T → T}

/-- A relation preserving observations and actions transports an exact execution. -/
theorem Run.simulate (R : S → T → Prop)
    (ho : ∀ s t, R s t → o' t = o s)
    (ha : ∀ a s t, R s t → R (act a s) (act' a t))
    {q : Q ⊕ E} {s t : S} {n : ℕ} {v : α}
    (h : c.Run out o act q s n v t) (u : T) (hu : R s u) :
    ∃ w, R t w ∧ c.Run out o' act' q u n v w := by
  induction h generalizing u with
  | done e s => exact ⟨u, hu, Run.done e u⟩
  | step q s h ih =>
    have he := ho s u hu
    obtain ⟨w, hw, hr⟩ := ih (act' (c.next q (o s)).1 u) (ha _ s u hu)
    exact ⟨w, hw, Run.step q u (by simpa only [he] using hr)⟩

variable {a : A → S → S} {a' : A → T → T}

/-- Forget semantic information which does not affect observations or actions. -/
theorem Run.map (f : S → T) (ho : ∀ s, o' (f s) = o s)
    (ha : ∀ v s, a' v (f s) = f (a v s))
    {q : Q ⊕ E} {s t : S} {n : ℕ} {v : α}
    (h : c.Run out o a q s n v t) : c.Run out o' a' q (f s) n v (f t) := by
  obtain ⟨w, rfl, hr⟩ := h.simulate (fun s t ↦ t = f s)
    (by rintro s _ rfl; exact ho s) (by rintro v s _ rfl; exact ha v s) (f s) rfl
  exact hr

/-- Add ghost information while preserving the control labels and exact cost. -/
theorem Run.lift (f : T → S) (ho : ∀ s, o' s = o (f s))
    (ha : ∀ v s, f (a' v s) = a v (f s))
    {q : Q ⊕ E} {s t : S} {n : ℕ} {v : α}
    (h : c.Run out o a q s n v t) (u : T) (hu : f u = s) :
    ∃ w, f w = t ∧ c.Run out o' a' q u n v w :=
  h.simulate (fun s t ↦ f t = s)
    (by rintro _ t rfl; exact ho t) (by rintro v _ t rfl; exact ha v t) u hu

end Control

end Complexity.Program
