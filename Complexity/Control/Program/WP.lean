/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Map
public import Std.WP
public import Std.Tactic.Do

/-!
# Total specifications for finite control programs

The interpretation of a program is fixed only for verification. Its syntax remains independent
of the input and of resource bookkeeping. The natural number in assertions is the remaining
budget. A weakest precondition requires an actual finite execution within that budget.
The interpreted state may contain further ghost data, such as visited memory addresses.
-/

@[expose] public section

namespace Complexity.Program

open Std.WP Lean.Order

variable {O A Op S α β : Type} {Ret : Op → Type}

/-- A predicate family registered for invariant elaboration by `vcgen`.
The index may be a carried value or the semantic state itself. -/
@[spec_invariant_type]
def Invariant (ι P : Type) := ι → P

/-- A program with the state interpretation used in a specification. -/
structure WithSemantics (e : Semantics O A Op Ret S) (α : Type) where
  /-- The same source program which is supplied to the compiler. -/
  code : Program O A Op Ret α

/-- Attach a state interpretation for verification, without changing the source program. -/
def verify (p : Program O A Op Ret α) (e : Semantics O A Op Ret S) : WithSemantics e α := ⟨p⟩

@[simp]
theorem verify_code (p : Program O A Op Ret α) (e : Semantics O A Op Ret S) :
    (p.verify e).code = p := rfl

/-- Expose an ordinary conditional to verification-condition generation. -/
@[spec]
theorem verify_ite (p : Prop) [Decidable p] (f g : Program O A Op Ret α)
    (e : Semantics O A Op Ret S) :
    (if p then f else g).verify e = if p then f.verify e else g.verify e := by
  split <;> rfl

/-- Expose a dependent conditional without discarding its branch hypotheses. -/
@[spec]
theorem verify_dite (p : Prop) [Decidable p] (f : p → Program O A Op Ret α)
    (g : ¬p → Program O A Op Ret α) (e : Semantics O A Op Ret S) :
    (dite p f g).verify e = dite p (fun h => (f h).verify e) (fun h => (g h).verify e) := by
  split <;> rfl

/-- Total execution within a remaining time budget. -/
def Total (p : Program O A Op Ret α) (e : Semantics O A Op Ret S)
    (Q : α → S → ℕ → Prop) (s : S) (b : ℕ) : Prop :=
  ∃ n a t, n ≤ b ∧ p.Exec e s n a t ∧ Q a t (b - n)

instance (e : Semantics O A Op Ret S) : WP (WithSemantics e α) α (S → ℕ → Prop) Unit where
  wpTrans p := ⟨fun Q _ => p.code.Total e Q⟩
  wp_trans_monotone p := by
    intro Q Q' x x' _ h s b ⟨n,a,t,hn,hr,hq⟩
    exact ⟨n,a,t,hn,hr,h a t (b - n) hq⟩

/-- Extract the finite execution guaranteed by a verified total specification. -/
theorem exec_of_spec {p : Program O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → ℕ → Prop} {Q : α → S → ℕ → Prop}
    (h : Triple (p.verify e) P Q ()) {s : S} {b : ℕ} (hs : P s b) :
    ∃ n a t, n ≤ b ∧ p.Exec e s n a t ∧ Q a t (b - n) :=
  h.le_wp s b hs

/-- Transport a total specification along a semantic relation, preserving its time budget. -/
theorem spec_simulate {T : Type} {e : Semantics O A Op Ret S}
    {e' : Semantics O A Op Ret T} (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {p : Program O A Op Ret α} {P : S → ℕ → Prop} {Q : α → S → ℕ → Prop}
    {P' : T → ℕ → Prop} {Q' : α → T → ℕ → Prop}
    (h : Triple (p.verify e) P Q ())
    (hp : ∀ t b, P' t b → ∃ s, P s b ∧ R s t)
    (hq : ∀ a s t b, R s t → Q a s b → Q' a t b)
    (he : e'.eval = e.eval := by rfl) :
    Triple (p.verify e') P' Q' () := by
  constructor
  intro t b ht
  obtain ⟨s, hs, hst⟩ := hp t b ht
  obtain ⟨n, a, u, hn, hr, hu⟩ := h.le_wp s b hs
  obtain ⟨v, huv, hv⟩ := Exec.simulate R ho ha hr t hst he
  exact ⟨n, a, v, hn, hv, hq a u v (b - n) huv hu⟩

/-- Extra time credits pass through a verified subprogram without changing its execution. -/
theorem frame_budget {p : Program O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → ℕ → Prop} {Q : α → S → ℕ → Prop}
    (h : Triple (p.verify e) P Q ()) (r : ℕ) :
    Triple (p.verify e)
      (fun s b ↦ ∃ c, P s c ∧ b = c + r)
      (fun a s b ↦ ∃ c, Q a s c ∧ b = c + r) () := by
  constructor
  rintro s b ⟨c, hc, rfl⟩
  obtain ⟨n, a, t, hn, he, hq⟩ := h.le_wp s c hc
  refine ⟨n, a, t, by omega, he, c - n, hq, ?_⟩
  omega

/-- An exact-budget subprogram may retain the credits reserved for its continuation. -/
theorem frame_budget_eq {p : Program O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → Prop} {Q : α → S → Prop} {n : ℕ}
    (h : Triple (p.verify e) (fun s b ↦ P s ∧ b = n)
      (fun a s b ↦ Q a s ∧ b = 0) ()) (r : ℕ) :
    Triple (p.verify e) (fun s b ↦ P s ∧ b = n + r)
      (fun a s b ↦ Q a s ∧ b = r) () := by
  constructor
  rintro s b ⟨hp, rfl⟩
  obtain ⟨m, a, t, hm, he, hq, hb⟩ := h.le_wp s n ⟨hp, rfl⟩
  refine ⟨m, a, t, by omega, he, hq, ?_⟩
  omega

/-- Returning a result performs no graph transition. -/
@[spec]
theorem spec_pure (a : α) (e : Semantics O A Op Ret S)
    (Q : α → S → ℕ → Prop) (x : Unit) :
    Triple ((Pure.pure (f := Program O A Op Ret) a).verify e) (Q a) Q x := by
  constructor
  intro s b h
  exact ⟨0,a,s,Nat.zero_le _,Exec.pure e a s,by simpa using h⟩

/-- Source binding composes executions without a dispatch transition. -/
@[spec]
theorem spec_bind (p : Program O A Op Ret α) (f : α → Program O A Op Ret β)
    (e : Semantics O A Op Ret S)
    (Q : β → S → ℕ → Prop) (x : Unit) :
    Triple ((p >>= f).verify e)
      (wp (p.verify e) (fun a => wp ((f a).verify e) Q x) x) Q x := by
  constructor
  rintro s b ⟨n,a,t,hn,hp,m,c,u,hm,hf,hq⟩
  refine ⟨n + m,c,u,by omega,Exec.bind hp hf,?_⟩
  convert hq using 1
  omega

set_option experimental.vcgen true in
/-- Compose two total contracts through the first program's postcondition. -/
theorem spec_bind_of_spec {p : Program O A Op Ret α} {f : α → Program O A Op Ret β}
    {e : Semantics O A Op Ret S} {P : S → ℕ → Prop}
    {R : α → S → ℕ → Prop} {Q : β → S → ℕ → Prop} {x : Unit}
    (hp : Triple (p.verify e) P R x)
    (hf : ∀ a, Triple ((f a).verify e) (R a) Q x) :
    Triple ((p >>= f).verify e) P Q x := by
  vcgen [hp, hf]

/-- Relabeling a result preserves the state and all remaining time credits. -/
theorem spec_mapResult (f : α → β) {p : Program O A Op Ret α}
    {e : Semantics O A Op Ret S} {P : S → ℕ → Prop} {Q : β → S → ℕ → Prop} {x : Unit}
    (h : Triple (p.verify e) P (fun a ↦ Q (f a)) x) :
    Triple (verify (p.mapResult β .value f) e) P Q x := by
  constructor
  intro s b hs
  obtain ⟨n, a, t, hn, he, hq⟩ := h.le_wp s b hs
  exact ⟨n, f a, t, hn, (by apply he.mapResult), hq⟩

/-- A primitive performs one local action and consumes one unit of budget. -/
@[spec]
theorem spec_perform (o : Op) (e : Semantics O A Op Ret S)
    (s : S) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((perform o).verify e) (fun t c ↦ t = s ∧ c = b)
      (fun a t c ↦ a = (e.eval o (e.observe s)).2 ∧
        t = e.act (e.eval o (e.observe s)).1 s ∧ c = b - 1) x := by
  constructor
  rintro t c ⟨rfl, rfl⟩
  exact ⟨1, _, _, by omega, Exec.perform e o _, rfl, rfl, rfl⟩

/-- The raw one-step constructor with a return continuation obeys the same atomic rule. -/
@[spec]
theorem spec_step_pure (o : Op) (e : Semantics O A Op Ret S)
    (s : S) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((step o (Pure.pure (f := Program O A Op Ret))).verify e)
      (fun t c ↦ t = s ∧ c = b)
      (fun a t c ↦ a = (e.eval o (e.observe s)).2 ∧
        t = e.act (e.eval o (e.observe s)).1 s ∧ c = b - 1) x :=
  spec_perform o e s b h x

/-- Compose a block execution with its source continuation. The generic rule is not registered:
its continuation WP is intended for a caller-supplied contract. -/
theorem spec_callControl {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (k : Fin d → Program O A Op Ret α) (e : Semantics O A Op Ret S)
    (Q : α → S → ℕ → Prop) (x : Unit) :
    Triple ((callControl b k).verify e)
      (fun s z ↦ ∃ m j t, m ≤ z ∧ Control.Run b id e.observe e.act b.start s m j t ∧
        wp ((k j).verify e) Q x t (z - m)) Q x := by
  constructor
  rintro s z ⟨m, j, t, hm, hb, n, a, u, hn, hk, hq⟩
  refine ⟨m + n, a, u, by omega, Syntax.Exec.call b k hb hk, ?_⟩
  convert hq using 1
  omega

/-- A block with a return continuation exposes its exact result, state, and unused credits. -/
@[spec]
theorem spec_callControl_pure {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (e : Semantics O A Op Ret S) (s t : S) (m z : ℕ) (j : Fin d)
    (hr : Control.Run b id e.observe e.act b.start s m j t) (hz : m ≤ z) (x : Unit) :
    Triple ((callControl b (Pure.pure (f := Program O A Op Ret))).verify e)
      (fun u q ↦ u = s ∧ q = z)
      (fun i u q ↦ i = j ∧ u = t ∧ q = z - m) x := by
  constructor
  rintro u q ⟨rfl, rfl⟩
  refine ⟨m, j, t, hz, ?_, rfl, rfl, rfl⟩
  exact Syntax.Exec.call (e := e) b (fun i ↦ Program.pure i) hr
    (Syntax.Exec.ret (v := .value) j t)

end Complexity.Program
