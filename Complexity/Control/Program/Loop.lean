/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.WP

/-! # Total specifications for loops

Numbered loops share one total-correctness rule. Repeat-until and finite-value loops derive
their specifications from it, preserving exact dispatch costs. Only the carried input and
output values use `FinEnum`; each body's control labels remain structural.
-/

@[expose] public section

namespace Complexity.Program

open Std.WP

variable {O A Op S α β : Type} {Ret : Op → Type}

/-- An invariant-local no-op removes the dispatch action from a body's precondition. -/
private theorem spec_nop_pre (a : A) {p : Program O A Op Ret α}
    {e : Semantics O A Op Ret S} {I : S → ℕ → Prop} {Q : α → S → ℕ → Prop} {x : Unit}
    (ha : ∀ s b, I s b → e.act a s = s)
    (h : Triple (p.verify e) (fun s b ↦ I s (b + 1)) Q x) :
    Triple (p.verify e) (fun s b ↦ ∃ t, I t (b + 1) ∧ s = e.act a t) Q x := by
  constructor
  rintro s b ⟨t, ht, rfl⟩
  simpa only [ha t (b + 1) ht] using h.le_wp t b ht

/-- A total loop rule. Every entry consumes a budget unit before executing its body. -/
@[spec]
theorem spec_loop {n r : ℕ} (a : A) (f : Fin n → Program O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (Q : Fin r → S → ℕ → Prop) (x : Unit)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verify e)
      (fun s b => ∃ t, I i t (b + 1) ∧ s = e.act a t)
      (fun j s b => match j with | .inl k => I k s b | .inr k => Q k s b) x) :
    Triple ((loop a f i).verify e) (I i) Q x := by
  constructor
  intro s b hs
  induction b using Nat.strong_induction_on generalizing i s with
  | h b ih =>
    have hb := hpos i s b hs
    have hr := (hstep i).le_wp (e.act a s) (b - 1) ⟨s,by simpa [Nat.sub_add_cancel hb] using hs,rfl⟩
    obtain ⟨m,j,t,hm,hr,hq⟩ := hr
    cases j with
    | inl j =>
      obtain ⟨l,k,u,hl,hj,hq⟩ := ih ((b - 1) - m) (by omega) j t hq
      refine ⟨m + l + 1,k,u,by omega,Exec.loop_next a f hr hj,?_⟩
      convert hq using 1
      omega
    | inr j =>
      refine ⟨m + 1,j,t,by omega,Exec.loop_done a f hr,?_⟩
      convert hq using 1
      omega

/-- A dispatcher need only preserve states satisfying the current loop invariant. -/
theorem spec_loop_nop_of_invariant {n r : ℕ}
    (a : A) (f : Fin n → Program O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (Q : Fin r → S → ℕ → Prop) (x : Unit)
    (ha : ∀ i s b, I i s b → e.act a s = s)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verify e)
      (fun s b => I i s (b + 1))
      (fun j s b => match j with | .inl k => I k s b | .inr k => Q k s b) x) :
    Triple ((loop a f i).verify e) (I i) Q x := by
  apply spec_loop a f i e I Q x hpos
  intro j
  exact spec_nop_pre a (ha j) (hstep j)

/-- For a semantic no-op, a loop body starts in the same state with one fewer credit. -/
theorem spec_loop_nop {n r : ℕ} (a : A) (f : Fin n → Program O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (Q : Fin r → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s, e.act a s = s)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verify e)
      (fun s b => I i s (b + 1))
      (fun j s b => match j with | .inl k => I k s b | .inr k => Q k s b) x) :
    Triple ((loop a f i).verify e) (I i) Q x :=
  spec_loop_nop_of_invariant a f i e I Q x (fun _ s _ _ ↦ ha s) hpos hstep

/-- A total repeat-until rule, including the action executed before each body entry. -/
@[spec]
theorem spec_repeatUntil (a : A) (p : Program O A Op Ret Bool) (e : Semantics O A Op Ret S)
    (I : Invariant S (ℕ → Prop)) (Q : Unit → S → ℕ → Prop) (x : Unit)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verify e)
      (fun s b => ∃ t, I t (b + 1) ∧ s = e.act a t)
      (fun r s b => if r then Q () s b else I s b) x) :
    Triple ((repeatUntil a p).verify e) (fun s b => I s b) Q x := by
  unfold repeatUntil
  apply spec_bind_of_spec (R := fun _ : Fin 1 ↦ Q ())
  · apply spec_loop a _ 0 e (fun _ ↦ I) (fun _ ↦ Q ()) x (fun _ ↦ hpos)
    intro _
    apply spec_bind_of_spec hstep
    intro r
    constructor
    intro s b hs
    apply (spec_pure _ e _ x).le_wp s b
    cases r <;> simpa using hs
  · intro _
    exact spec_pure () e Q x

/-- A repeat dispatcher need only preserve states satisfying its invariant. -/
theorem spec_repeatUntil_nop_of_invariant
    (a : A) (p : Program O A Op Ret Bool) (e : Semantics O A Op Ret S)
    (I : Invariant S (ℕ → Prop)) (Q : Unit → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s b, I s b → e.act a s = s)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verify e) (fun s b => I s (b + 1))
      (fun r s b => if r then Q () s b else I s b) x) :
    Triple ((repeatUntil a p).verify e) (fun s b => I s b) Q x := by
  apply spec_repeatUntil a p e I Q x hpos
  exact spec_nop_pre a ha hstep

/-- A no-op dispatcher changes only the remaining time budget. -/
theorem spec_repeatUntil_nop (a : A) (p : Program O A Op Ret Bool) (e : Semantics O A Op Ret S)
    (I : Invariant S (ℕ → Prop)) (Q : Unit → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s, e.act a s = s)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verify e) (fun s b => I s (b + 1))
      (fun r s b => if r then Q () s b else I s b) x) :
    Triple ((repeatUntil a p).verify e) (fun s b => I s b) Q x :=
  spec_repeatUntil_nop_of_invariant a p e I Q x (fun s _ _ ↦ ha s) hpos hstep

variable [FinEnum α] [FinEnum β]

/-- Encode a body's carried result without enumerating its control states. -/
def loopOnBody (b : α → Program O A Op Ret (α ⊕ β)) (i : Fin (FinEnum.card α)) :
    Syntax O A Op Ret β (.branch (FinEnum.card α) (FinEnum.card β)) :=
  (b (FinEnum.equiv.symm i)).mapResult β (.branch (FinEnum.card α) (FinEnum.card β))
    (Sum.map FinEnum.equiv FinEnum.equiv)

/-- A finite-value loop. Every body entry executes the charged dispatch action. -/
def loopOn (a : A) (b : α → Program O A Op Ret (α ⊕ β)) (i : α) :
    Program O A Op Ret β :=
  Syntax.loop a (FinEnum.equiv i) (loopOnBody b)
    (fun j ↦ Syntax.ret (u := .value) ((FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm j))

/-- Finite carried values are a relabeling of the numbered loop's inputs and results. -/
theorem loopOn_eq_mapResult_loop (a : A) (b : α → Program O A Op Ret (α ⊕ β)) (i : α) :
    loopOn a b i =
      (loop a (fun j ↦ (b (FinEnum.equiv.symm j)).mapResult _ .value
        (Sum.map FinEnum.equiv FinEnum.equiv)) (FinEnum.equiv i)).mapResult β .value
        (FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm := by
  simp only [loopOn, loop, Syntax.mapResult, Syntax.mapResult_comp,
    Function.id_comp]
  rfl

namespace Exec

variable {e : Semantics O A Op Ret S}

/-- Finishing a finite-value loop includes its dispatch transition. -/
theorem loopOn_done (a : A) (b : α → Program O A Op Ret (α ⊕ β))
    {i : α} {j : β} {s t : S} {n : ℕ}
    (h : (b i).Exec e (e.act a s) n (.inr j) t) :
    (loopOn a b i).Exec e s (n + 1) j t := by
  have hb := h.mapResult (β := β) (w := .branch (FinEnum.card α) (FinEnum.card β))
    (Sum.map FinEnum.equiv FinEnum.equiv)
  apply Syntax.Exec.loop_done (m := n) (l := 0) (j := FinEnum.equiv j)
    a (FinEnum.equiv i) (loopOnBody b)
    (fun j ↦ Syntax.ret (u := .value) ((FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm j))
  · simpa only [loopOnBody, Equiv.symm_apply_apply, Sum.map_inr] using hb
  · simpa only [Equiv.symm_apply_apply] using
      (Syntax.Exec.ret (e := e) (α := β) (v := .value)
        ((FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm (FinEnum.equiv j)) t)

/-- Continuing routes to the next external carried value without a connecting action. -/
theorem loopOn_next (a : A) (b : α → Program O A Op Ret (α ⊕ β))
    {i j : α} {s t u : S} {n m : ℕ} {v : β}
    (h : (b i).Exec e (e.act a s) n (.inl j) t)
    (hc : (loopOn a b j).Exec e t m v u) :
    (loopOn a b i).Exec e s (n + m + 1) v u := by
  have hb := h.mapResult (β := β) (w := .branch (FinEnum.card α) (FinEnum.card β))
    (Sum.map FinEnum.equiv FinEnum.equiv)
  apply Syntax.Exec.loop_next (m := n) (l := m) (j := FinEnum.equiv j)
    a (FinEnum.equiv i) (loopOnBody b)
    (fun j ↦ Syntax.ret (u := .value) ((FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm j))
  · simpa only [loopOnBody, Equiv.symm_apply_apply, Sum.map_inl] using hb
  · exact hc

end Exec

/-- A total rule for finite carried values; budget pays for every traversal of a back edge. -/
@[spec]
theorem spec_loopOn (a : A) (b : α → Program O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (Q : β → S → ℕ → Prop)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verify e)
      (fun s n ↦ ∃ t, I i t (n + 1) ∧ s = e.act a t)
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => Q j s n) ()) :
    Triple ((loopOn a b i).verify e) (I i) Q () := by
  rw [loopOn_eq_mapResult_loop]
  apply spec_mapResult
  have h := spec_loop a
    (fun j ↦ (b (FinEnum.equiv.symm j)).mapResult _ .value
      (Sum.map FinEnum.equiv FinEnum.equiv))
    (FinEnum.equiv i) e (fun j ↦ I (FinEnum.equiv.symm j))
    (fun j ↦ Q (FinEnum.equiv.symm j)) () (fun j ↦ hp (FinEnum.equiv.symm j))
  simp only [Equiv.symm_apply_apply] at h
  apply h
  intro j
  apply spec_mapResult
  constructor
  apply Triple.entails_wp_of_post (hb (FinEnum.equiv.symm j))
  intro r s n hr
  cases r <;> simpa only [Sum.map_inl, Sum.map_inr, Equiv.symm_apply_apply] using hr

/-- The finite-value dispatcher may be a no-op only on invariant states. -/
theorem spec_loopOn_nop_of_invariant
    (a : A) (b : α → Program O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (Q : β → S → ℕ → Prop)
    (ha : ∀ i s n, I i s n → e.act a s = s)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verify e) (fun s n ↦ I i s (n + 1))
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => Q j s n) ()) :
    Triple ((loopOn a b i).verify e) (I i) Q () := by
  apply spec_loopOn a b i e I Q hp
  intro j
  exact spec_nop_pre a (ha j) (hb j)

/-- A globally inert finite-value dispatcher specializes the invariant-local rule. -/
theorem spec_loopOn_nop (a : A) (b : α → Program O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (Q : β → S → ℕ → Prop)
    (ha : ∀ s, e.act a s = s)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verify e) (fun s n ↦ I i s (n + 1))
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => Q j s n) ()) :
    Triple ((loopOn a b i).verify e) (I i) Q () :=
  spec_loopOn_nop_of_invariant a b i e I Q (fun _ s _ _ ↦ ha s) hp hb

end Complexity.Program
