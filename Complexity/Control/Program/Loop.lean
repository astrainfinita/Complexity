/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.WP

/-! # Total specifications for loops

Numbered loops share one total-correctness rule. Repeat-until and finite-value loops derive
their specifications from it, preserving exact dispatch costs. For proofs by induction on the
iterations, `execWithinWith_repeatUntilWith_add` unfolds one iteration of a repeat-until loop with
the budgets added; `execWithinWith_repeatUntilWith_done` and `execWithinWith_repeatUntilWith_next`
are its cases for a body that returns `true` or `false`. Only the carried input and output values
use `FinEnum`; each body's control labels remain structural.
-/

@[expose] public section

namespace Complexity.Program

open Std.WP

variable {F : Type → Type} {O A Op S α β : Type} {Ret : Op → Type} {m : Type → Type} [Monad m]
  {Q : MonadQuant m}

section Rules

variable [MonadLiftT F m]

/-- A dispatcher preserving the invariant satisfies the body's precondition. -/
private theorem spec_dispatch_pre (a : A) {p : Program F O A Op Ret α}
    {e : Semantics O A Op Ret S} {I : S → ℕ → Prop} {R : α → S → ℕ → Prop} {x : Unit}
    (ha : ∀ s b, I s b → I (e.act a s) b)
    (h : Triple (p.verifyWith m Q e) (fun s b ↦ I s (b + 1)) R x) :
    Triple (p.verifyWith m Q e) (fun s b ↦ ∃ t, I t (b + 1) ∧ s = e.act a t) R x := by
  constructor
  rintro s b ⟨t, ht, rfl⟩
  exact h.le_wp (e.act a t) b (ha t (b + 1) ht)

/-- A total loop rule. Every entry consumes a budget unit before executing its body. -/
@[spec]
theorem spec_loop {n r : ℕ} (a : A) (f : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (R : Fin r → S → ℕ → Prop) (x : Unit)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verifyWith m Q e)
      (fun s b => ∃ t, I i t (b + 1) ∧ s = e.act a t)
      (fun j s b => match j with | .inl k => I k s b | .inr k => R k s b) x) :
    Triple ((loop a f i).verifyWith m Q e) (I i) R x := by
  constructor
  intro s b hs
  induction b using Nat.strong_induction_on generalizing i s with
  | h b ih =>
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.mpr (hpos i s b hs)
    have hb := ((hstep i).le_wp (e.act a s) b ⟨s, hs, rfl⟩).with_le
    exact Syntax.ExecWithinWith.loop a i _ _ s b (hb.mapResult (w := .branch n r) id)
      (fun j t c ⟨_, rfl, hc, hI⟩ ↦ ih c (by omega) j t hI)
      (fun j t c ⟨_, rfl, _, hQ⟩ ↦ .ret (v := .value) j t c hQ)

/-- A dispatcher preserving the loop invariant leaves the body precondition unchanged. -/
theorem spec_loop_of_invariant {n r : ℕ}
    (a : A) (f : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (R : Fin r → S → ℕ → Prop) (x : Unit)
    (ha : ∀ i s b, I i s b → I i (e.act a s) b)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verifyWith m Q e)
      (fun s b => I i s (b + 1))
      (fun j s b => match j with | .inl k => I k s b | .inr k => R k s b) x) :
    Triple ((loop a f i).verifyWith m Q e) (I i) R x := by
  apply spec_loop a f i e I R x hpos
  intro j
  exact spec_dispatch_pre a (ha j) (hstep j)

/-- For a semantic no-op, a loop body starts in the same state with one fewer credit. -/
theorem spec_loop_nop {n r : ℕ} (a : A) (f : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) (e : Semantics O A Op Ret S) (I : Invariant (Fin n) (S → ℕ → Prop))
    (R : Fin r → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s, e.act a s = s)
    (hpos : ∀ i s b, I i s b → 0 < b)
    (hstep : ∀ i, Triple ((f i).verifyWith m Q e)
      (fun s b => I i s (b + 1))
      (fun j s b => match j with | .inl k => I k s b | .inr k => R k s b) x) :
    Triple ((loop a f i).verifyWith m Q e) (I i) R x :=
  spec_loop_of_invariant a f i e I R x (fun _ s _ hs ↦ by simpa only [ha s] using hs) hpos hstep

/-- A total repeat-until rule, including the action executed before each body entry. -/
@[spec]
theorem spec_repeatUntilWith (a : A) (p : Program F O A Op Ret Bool) (e : Semantics O A Op Ret S)
    (I : Invariant S (ℕ → Prop)) (R : Unit → S → ℕ → Prop) (x : Unit)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verifyWith m Q e)
      (fun s b => ∃ t, I t (b + 1) ∧ s = e.act a t)
      (fun r s b => if r then R () s b else I s b) x) :
    Triple ((repeatUntilWith a p).verifyWith m Q e) (fun s b => I s b) R x := by
  unfold repeatUntilWith
  apply spec_bind_of_spec
  · apply spec_loop a _ 0 e (fun _ ↦ I) (fun _ ↦ R ()) x (fun _ ↦ hpos)
    intro _
    apply spec_bind_of_spec hstep
    intro r
    constructor
    intro s b hs
    apply (spec_pure _ e _ x).le_wp s b
    cases r <;> simpa using hs
  · intro _
    exact spec_pure () e R x

/-- A repeat dispatcher may update the state while preserving its invariant. -/
theorem spec_repeatUntilWith_of_invariant
    (a : A) (p : Program F O A Op Ret Bool) (e : Semantics O A Op Ret S)
    (I : Invariant S (ℕ → Prop)) (R : Unit → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s b, I s b → I (e.act a s) b)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verifyWith m Q e) (fun s b => I s (b + 1))
      (fun r s b => if r then R () s b else I s b) x) :
    Triple ((repeatUntilWith a p).verifyWith m Q e) (fun s b => I s b) R x := by
  apply spec_repeatUntilWith a p e I R x hpos
  exact spec_dispatch_pre a ha hstep

/-- A no-op dispatcher changes only the remaining time budget. -/
theorem spec_repeatUntilWith_nop (a : A) (p : Program F O A Op Ret Bool)
    (e : Semantics O A Op Ret S) (I : Invariant S (ℕ → Prop)) (R : Unit → S → ℕ → Prop) (x : Unit)
    (ha : ∀ s, e.act a s = s)
    (hpos : ∀ s b, I s b → 0 < b)
    (hstep : Triple (p.verifyWith m Q e) (fun s b => I s (b + 1))
      (fun r s b => if r then R () s b else I s b) x) :
    Triple ((repeatUntilWith a p).verifyWith m Q e) (fun s b => I s b) R x :=
  spec_repeatUntilWith_of_invariant a p e I R x
    (fun s _ hs ↦ by simpa only [ha s] using hs) hpos hstep

/-- One iteration of a repeat-until loop takes the dispatch and the body: where the body returns
`true` the loop has finished, and where it returns `false` the loop runs again. Budgets add; the
postconditions do not read the remaining budget. -/
theorem execWithinWith_repeatUntilWith_add {a : A} {p : Program F O A Op Ret Bool}
    {e : Semantics O A Op Ret S} {s : S} {n k : ℕ} {P : Bool → S → Prop} {R : S → Prop}
    (hp : Syntax.ExecWithinWith m Q e p (e.act a s) n fun r t _ ↦ P r t)
    (hdone : ∀ t, P true t → R t)
    (hnext : ∀ t, P false t →
      Syntax.ExecWithinWith m Q e (repeatUntilWith a p) t k fun _ u _ ↦ R u) :
    Syntax.ExecWithinWith m Q e (repeatUntilWith a p) s (n + k + 1) fun _ u _ ↦ R u := by
  let P' (r : Fin 1 ⊕ Fin 1) (t : S) (c : ℕ) : Prop :=
    r.elim (fun _ ↦ Syntax.ExecWithinWith m Q e (repeatUntilWith a p) t c fun _ u _ ↦ R u)
      fun _ ↦ R t
  have hp' : p.ExecWithinWith m Q e (e.act a s) (n + k) fun r ↦
      P' (if r then .inr 0 else .inl 0) := by
    refine (hp.add_budget k).mono ?_
    rintro r t _ ⟨d, hP, rfl⟩
    cases r
    · exact (hnext t hP).mono_budget (Nat.le_add_left k d)
    · exact hdone t hP
  refine Syntax.ExecWithinWith.loop a 0 _ _ s (n + k) (P := P') ?_ (fun j t c hr ↦ ?_)
    fun _ t c hr ↦ .ret (v := .value) () t c hr
  · refine (((hp'.bindTo fun r t c hr ↦ .ret (v := .value) _ t c hr).mapResult
      (β := Fin 1) (w := .branch 1 1) id).mapResult (β := Unit) (w := .branch 1 1) id).mono ?_
    rintro _ _ _ ⟨_, rfl, _, rfl, hr⟩
    exact hr
  · obtain rfl := Subsingleton.elim j 0
    exact hr

/-- A body returning `true` finishes a repeat-until loop after one dispatch. -/
theorem execWithinWith_repeatUntilWith_done {a : A} {p : Program F O A Op Ret Bool}
    {e : Semantics O A Op Ret S} {s : S} {n : ℕ} {R : S → Prop}
    (hp : Syntax.ExecWithinWith m Q e p (e.act a s) n fun r t _ ↦ r = true ∧ R t) :
    Syntax.ExecWithinWith m Q e (repeatUntilWith a p) s (n + 1) fun _ u _ ↦ R u :=
  execWithinWith_repeatUntilWith_add (k := 0) hp (fun _ h ↦ h.2) fun _ h ↦ nomatch h.1

/-- After a body returning `false`, a repeat-until loop dispatches and runs again. -/
theorem execWithinWith_repeatUntilWith_next {a : A} {p : Program F O A Op Ret Bool}
    {e : Semantics O A Op Ret S} {s : S} {n k : ℕ} {P R : S → Prop}
    (hp : Syntax.ExecWithinWith m Q e p (e.act a s) n fun r t _ ↦ r = false ∧ P t)
    (hnext : ∀ t, P t → Syntax.ExecWithinWith m Q e (repeatUntilWith a p) t k fun _ u _ ↦ R u) :
    Syntax.ExecWithinWith m Q e (repeatUntilWith a p) s (n + k + 1) fun _ u _ ↦ R u :=
  execWithinWith_repeatUntilWith_add hp (fun _ h ↦ nomatch h.1) fun t h ↦ hnext t h.2

end Rules

section LoopOn

variable [FinEnum α] [FinEnum β]

/-- Encode a body's carried result without enumerating its control states. -/
def loopOnBody (b : α → Program F O A Op Ret (α ⊕ β)) (i : Fin (FinEnum.card α)) :
    Syntax F O A Op Ret β (.branch (FinEnum.card α) (FinEnum.card β)) :=
  (b (FinEnum.equiv.symm i)).mapResult β (.branch (FinEnum.card α) (FinEnum.card β))
    (Sum.map FinEnum.equiv FinEnum.equiv)

/-- A finite-value loop with an explicit dispatch action and a carried value.

As in `loop`, `dispatch` runs before every body entry and costs one transition. The caller
chooses it because `A` has no assumed no-op. Only carried values need `FinEnum`; the
compiled control labels remain structural. -/
def loopOn (dispatch : A) (b : α → Program F O A Op Ret (α ⊕ β)) (i : α) :
    Program F O A Op Ret β :=
  Syntax.loop dispatch (FinEnum.equiv i) (loopOnBody b)
    (fun j ↦ Syntax.ret ((FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm j))

/-- Finite carried values are a relabeling of the numbered loop's inputs and results. -/
theorem loopOn_eq_mapResult_loop (a : A) (b : α → Program F O A Op Ret (α ⊕ β)) (i : α) :
    loopOn a b i =
      (loop a (fun j ↦ (b (FinEnum.equiv.symm j)).mapResult _ .value
        (Sum.map FinEnum.equiv FinEnum.equiv)) (FinEnum.equiv i)).mapResult β .value
        (FinEnum.equiv : β ≃ Fin (FinEnum.card β)).symm := by
  simp only [loopOn, loop, Syntax.mapResult, Syntax.mapResult_comp,
    Function.id_comp]
  rfl

variable [MonadLiftT F m]

/-- A total rule for finite carried values; budget pays for every traversal of a back edge. -/
@[spec]
theorem spec_loopOn (a : A) (b : α → Program F O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (R : β → S → ℕ → Prop)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verifyWith m Q e)
      (fun s n ↦ ∃ t, I i t (n + 1) ∧ s = e.act a t)
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => R j s n) ()) :
    Triple ((loopOn a b i).verifyWith m Q e) (I i) R () := by
  rw [loopOn_eq_mapResult_loop]
  apply spec_mapResult
  have h := spec_loop (Q := Q) a
    (fun j ↦ (b (FinEnum.equiv.symm j)).mapResult _ .value
      (Sum.map FinEnum.equiv FinEnum.equiv))
    (FinEnum.equiv i) e (fun j ↦ I (FinEnum.equiv.symm j))
    (fun j ↦ R (FinEnum.equiv.symm j)) () (fun j ↦ hp (FinEnum.equiv.symm j))
  simp only [Equiv.symm_apply_apply] at h
  apply h
  intro j
  apply spec_mapResult
  constructor
  apply Triple.entails_wp_of_post (hb (FinEnum.equiv.symm j))
  intro r s n hr
  cases r <;> simpa only [Sum.map_inl, Sum.map_inr, Equiv.symm_apply_apply] using hr

/-- A finite-value dispatcher may update the state while preserving the carried invariant. -/
theorem spec_loopOn_of_invariant
    (a : A) (b : α → Program F O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (R : β → S → ℕ → Prop)
    (ha : ∀ i s n, I i s n → I i (e.act a s) n)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verifyWith m Q e) (fun s n ↦ I i s (n + 1))
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => R j s n) ()) :
    Triple ((loopOn a b i).verifyWith m Q e) (I i) R () := by
  apply spec_loopOn a b i e I R hp
  intro j
  exact spec_dispatch_pre a (ha j) (hb j)

/-- A globally inert finite-value dispatcher specializes the invariant-local rule. -/
theorem spec_loopOn_nop (a : A) (b : α → Program F O A Op Ret (α ⊕ β)) (i : α)
    (e : Semantics O A Op Ret S) (I : Invariant α (S → ℕ → Prop)) (R : β → S → ℕ → Prop)
    (ha : ∀ s, e.act a s = s)
    (hp : ∀ i s n, I i s n → 0 < n)
    (hb : ∀ i, Triple ((b i).verifyWith m Q e) (fun s n ↦ I i s (n + 1))
      (fun j s n ↦ match j with | .inl j => I j s n | .inr j => R j s n) ()) :
    Triple ((loopOn a b i).verifyWith m Q e) (I i) R () :=
  spec_loopOn_of_invariant a b i e I R (fun _ s _ hs ↦ by simpa only [ha s] using hs) hp hb

end LoopOn

end Complexity.Program
