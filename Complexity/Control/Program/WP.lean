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
# Specifications for finite control programs

The interpretation of a program is fixed only for verification. Its syntax remains independent
of the input and of resource bookkeeping. The natural number in assertions is the remaining
budget. The interpreted state may contain further ghost data, such as visited memory addresses.

`p.verifyWith m Q e` attaches the interpretation `e` of the operations, the interpretation `m` of
the choices and a quantifier `Q` on `m`. A weakest precondition asks for an execution within the
remaining budget (`Syntax.ExecWithinWith`): with `MonadQuant.all` every run finishes within the
budget with the postcondition, with `MonadQuant.any` some run does. `p.verify e`, for a
deterministic program, is `p.verifyWith Id .all e`, and the rules below serve every quantifier. A
deterministic program embedded by `ofId` keeps its `verify` specification under a quantifier that
reads the lift of `Pure.pure a` as `a` (`spec_ofId`).

For `vcgen`, a choice under `MonadQuant.all` has a registered rule whose postcondition records
that the chosen value is one of the choices. Under `MonadQuant.any` the caller supplies the chosen
value to the unregistered rule `spec_chooseWith_any` (or `spec_chooseAct_any`). For other
quantifiers the general rules `spec_chooseAct` and `spec_chooseWith` state the quantifier of the
continuation.
-/

@[expose] public section

namespace Complexity.Program

open Std.WP Lean.Order

variable {F : Type → Type} {O A Op S α β : Type} {Ret : Op → Type}

/-- A predicate family registered for invariant elaboration by `vcgen`.
The index may be a carried value or the semantic state itself. -/
@[spec_invariant_type]
def Invariant (ι P : Type) := ι → P

/-- A program with the interpretations of its operations and choices used in a specification, and
the quantifier reading its outcomes. -/
structure WithSemanticsWith (F : Type → Type) (m : Type → Type) [Monad m] (Q : MonadQuant m)
    (e : Semantics O A Op Ret S) (α : Type) where
  /-- The same source program which is supplied to the compiler. -/
  code : Program F O A Op Ret α

/-- Attach the interpretations and the quantifier for verification, without changing the
program. -/
def verifyWith (p : Program F O A Op Ret α) (m : Type → Type) [Monad m] (Q : MonadQuant m)
    (e : Semantics O A Op Ret S) : WithSemanticsWith F m Q e α :=
  ⟨p⟩

/-- Attach the interpretation of a deterministic program for verification: its run finishes
within the budget. -/
abbrev verify (p : Program Id O A Op Ret α) (e : Semantics O A Op Ret S) :
    WithSemanticsWith Id Id .all e α :=
  p.verifyWith Id .all e

variable {m : Type → Type} [Monad m] {Q : MonadQuant m}

@[simp]
theorem verifyWith_code (p : Program F O A Op Ret α) (e : Semantics O A Op Ret S) :
    (p.verifyWith m Q e).code = p := rfl

/-- Expose an ordinary conditional to verification-condition generation. -/
@[spec]
theorem verifyWith_ite (p : Prop) [Decidable p] (f g : Program F O A Op Ret α)
    (e : Semantics O A Op Ret S) :
    (if p then f else g).verifyWith m Q e =
      if p then f.verifyWith m Q e else g.verifyWith m Q e := by
  split <;> rfl

/-- Expose a dependent conditional without discarding its branch hypotheses. -/
@[spec]
theorem verifyWith_dite (p : Prop) [Decidable p] (f : p → Program F O A Op Ret α)
    (g : ¬p → Program F O A Op Ret α) (e : Semantics O A Op Ret S) :
    (dite p f g).verifyWith m Q e =
      dite p (fun h ↦ (f h).verifyWith m Q e) (fun h ↦ (g h).verifyWith m Q e) := by
  split <;> rfl

variable [MonadLiftT F m]

instance instWPWithSemanticsWith (e : Semantics O A Op Ret S) :
    WP (WithSemanticsWith F m Q e α) α (S → ℕ → Prop) Unit where
  wpTrans p := ⟨fun R _ s b ↦ p.code.ExecWithinWith m Q e s b R⟩
  wp_trans_monotone _ := fun _ _ _ _ _ h _ _ hp ↦ hp.mono fun a t b' hr ↦ h a t b' hr

/-- The instance above at `Id` and `MonadQuant.all`, the case of `p.verify e`. It is a shortcut for
instance synthesis, which otherwise finds `Pure Id`, `Monad Id` and `MonadLiftT Id Id` again at
every specification of a deterministic program. -/
instance (e : Semantics O A Op Ret S) :
    WP (WithSemanticsWith Id Id .all e α) α (S → ℕ → Prop) Unit :=
  instWPWithSemanticsWith e

/-- Extract the execution within the budget guaranteed by a verified specification. -/
theorem execWithinWith_of_spec {p : Program F O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → ℕ → Prop} {R : α → S → ℕ → Prop}
    (h : Triple (p.verifyWith m Q e) P R ()) {s : S} {b : ℕ} (hs : P s b) :
    p.ExecWithinWith m Q e s b R :=
  h.le_wp s b hs

/-- Transport a specification along a semantic relation, preserving its time budget. -/
theorem spec_simulate {T : Type} {e : Semantics O A Op Ret S}
    {e' : Semantics O A Op Ret T} (R : S → T → Prop)
    (ho : ∀ s t, R s t → e'.observe t = e.observe s)
    (ha : ∀ a s t, R s t → R (e.act a s) (e'.act a t))
    {p : Program F O A Op Ret α} {P : S → ℕ → Prop} {P₁ : α → S → ℕ → Prop}
    {P' : T → ℕ → Prop} {P₁' : α → T → ℕ → Prop}
    (h : Triple (p.verifyWith m Q e) P P₁ ())
    (hp : ∀ t b, P' t b → ∃ s, P s b ∧ R s t)
    (hq : ∀ a s t b, R s t → P₁ a s b → P₁' a t b)
    (he : e'.eval = e.eval := by rfl) :
    Triple (p.verifyWith m Q e') P' P₁' () := by
  constructor
  intro t b ht
  obtain ⟨s, hs, hst⟩ := hp t b ht
  exact ((h.le_wp s b hs).simulate R ho ha t hst he).mono fun a u b' ⟨v, hv, hq'⟩ ↦
    hq a v u b' hv hq'

/-- Extra time credits pass through a verified subprogram without changing its executions. -/
theorem frame_budget {p : Program F O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → ℕ → Prop} {R : α → S → ℕ → Prop}
    (h : Triple (p.verifyWith m Q e) P R ()) (r : ℕ) :
    Triple (p.verifyWith m Q e)
      (fun s b ↦ ∃ c, P s c ∧ b = c + r)
      (fun a s b ↦ ∃ c, R a s c ∧ b = c + r) () := by
  constructor
  rintro s b ⟨c, hc, rfl⟩
  exact (h.le_wp s c hc).add_budget r

/-- An exact-budget subprogram may retain the credits reserved for its continuation. -/
theorem frame_budget_eq {p : Program F O A Op Ret α} {e : Semantics O A Op Ret S}
    {P : S → Prop} {R : α → S → Prop} {n : ℕ}
    (h : Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ b = n)
      (fun a s b ↦ R a s ∧ b = 0) ()) (r : ℕ) :
    Triple (p.verifyWith m Q e) (fun s b ↦ P s ∧ b = n + r)
      (fun a s b ↦ R a s ∧ b = r) () := by
  constructor
  rintro s b ⟨hp, rfl⟩
  exact ((h.le_wp s n ⟨hp, rfl⟩).add_budget r).mono fun _ _ _ ⟨_, ⟨hr, hc⟩, hb⟩ ↦
    ⟨hr, by omega⟩

/-- Returning a result performs no graph transition. -/
@[spec]
theorem spec_pure (a : α) (e : Semantics O A Op Ret S) (R : α → S → ℕ → Prop) (x : Unit) :
    Triple ((Pure.pure (f := Program F O A Op Ret) a).verifyWith m Q e) (R a) R x :=
  ⟨fun s b h ↦ Syntax.ExecWithinWith.ret (v := .value) a s b h⟩

/-- Source binding runs the continuation from every return, without a dispatch transition. -/
@[spec]
theorem spec_bind (p : Program F O A Op Ret α) (f : α → Program F O A Op Ret β)
    (e : Semantics O A Op Ret S) (R : β → S → ℕ → Prop) (x : Unit) :
    Triple ((p >>= f).verifyWith m Q e)
      (wp (p.verifyWith m Q e) (fun a ↦ wp ((f a).verifyWith m Q e) R x) x) R x :=
  ⟨fun _ _ hp ↦ Syntax.ExecWithinWith.bindTo hp fun _ _ _ hf ↦ hf⟩

set_option experimental.vcgen true in
/-- Compose two specifications through the first program's postcondition. -/
theorem spec_bind_of_spec {p : Program F O A Op Ret α} {f : α → Program F O A Op Ret β}
    {e : Semantics O A Op Ret S} {P : S → ℕ → Prop}
    {P₁ : α → S → ℕ → Prop} {R : β → S → ℕ → Prop} {x : Unit}
    (hp : Triple (p.verifyWith m Q e) P P₁ x)
    (hf : ∀ a, Triple ((f a).verifyWith m Q e) (P₁ a) R x) :
    Triple ((p >>= f).verifyWith m Q e) P R x := by
  vcgen [hp, hf]

/-- Relabeling a result preserves the state and all remaining time credits. -/
theorem spec_mapResult (f : α → β) {p : Program F O A Op Ret α}
    {e : Semantics O A Op Ret S} {P : S → ℕ → Prop} {R : β → S → ℕ → Prop} {x : Unit}
    (h : Triple (p.verifyWith m Q e) P (fun a ↦ R (f a)) x) :
    Triple (verifyWith (p.mapResult β .value f) m Q e) P R x :=
  ⟨fun s b hs ↦ ((h.le_wp s b hs).mapResult (w := .value) f).mono fun _ _ _ ⟨_, h, hr⟩ ↦
    h ▸ hr⟩

/-- A deterministic program embedded into a choice shape keeps its `verify` specification under
a quantifier reading the lift of `Pure.pure a` as `a`, so `vcgen` continues with the specification
registered for `p.verify e`. -/
@[spec]
theorem spec_ofId [Pure F] [MonadQuant.PureLiftT F m Q] (p : Program Id O A Op Ret α)
    (e : Semantics O A Op Ret S) (R : α → S → ℕ → Prop) (x : Unit) :
    Triple (verifyWith (p.ofId (F := F)) m Q e) (wp (p.verify e) R x) R x :=
  ⟨fun _ _ h ↦ Syntax.ExecWithin.ofId h⟩

/-- A primitive performs one local action and consumes one unit of budget. -/
@[spec]
theorem spec_perform (o : Op) (e : Semantics O A Op Ret S) (s : S) (b : ℕ) (h : 0 < b)
    (x : Unit) :
    Triple ((perform (F := F) o).verifyWith m Q e) (fun t c ↦ t = s ∧ c = b)
      (fun a t c ↦ a = (e.eval o (e.observe s)).2 ∧
        t = e.act (e.eval o (e.observe s)).1 s ∧ c = b - 1) x := by
  constructor
  rintro t c ⟨rfl, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_one.mpr h
  exact Syntax.ExecWithinWith.step o _ t c
    (.ret (v := .value) _ _ c ⟨rfl, rfl, (Nat.add_sub_cancel c 1).symm⟩)

/-- The raw one-step constructor with a return continuation obeys the same atomic rule. -/
@[spec]
theorem spec_step_pure (o : Op) (e : Semantics O A Op Ret S) (s : S) (b : ℕ) (h : 0 < b)
    (x : Unit) :
    Triple ((step (F := F) o Pure.pure).verifyWith m Q e) (fun t c ↦ t = s ∧ c = b)
      (fun a t c ↦ a = (e.eval o (e.observe s)).2 ∧
        t = e.act (e.eval o (e.observe s)).1 s ∧ c = b - 1) x :=
  spec_perform o e s b h x

/-- Compose a block execution with its source continuation. The generic rule is not registered:
its continuation WP is intended for a caller-supplied contract. -/
theorem spec_callControl {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Program F O A Op Ret α) (e : Semantics O A Op Ret S)
    (R : α → S → ℕ → Prop) (x : Unit) :
    Triple ((callControl b k).verifyWith m Q e)
      (fun s z ↦ b.RunWithin e.observe e.act (fun j t z' ↦ wp ((k j).verifyWith m Q e) R x t z')
        b.start s z) R x :=
  ⟨fun _ _ h ↦ Syntax.ExecWithinWith.call b k h⟩

/-- A choice of an action and a continuation consumes one unit of budget, and the quantifier
reads the continuation over the choices. Not registered. -/
theorem spec_chooseAct {d : ℕ} (c : F (A × Fin d)) (e : Semantics O A Op Ret S)
    (R : Fin d → S → ℕ → Prop) (x : Unit) :
    Triple ((chooseAct c).verifyWith m Q e)
      (fun s b ↦ 0 < b ∧ Q (fun r ↦ R r.2 (e.act r.1 s) (b - 1)) (monadLift c : m (A × Fin d)))
      R x := by
  constructor
  rintro s b ⟨hb, h⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.mpr hb
  exact Syntax.ExecWithinWith.choice c _ s b (Q.mono (fun r hr ↦ .ret (v := .value) r.2 _ b hr) h)

/-- A choice of a finite value consumes one unit of budget with its dispatch action, and the
quantifier reads the continuation over the values. Not registered. -/
theorem spec_chooseWith [Functor F] [LawfulMonad m] [LawfulFunctorLiftT F m] {β : Type}
    [FinEnum β] (dispatch : A) (c : F β) (e : Semantics O A Op Ret S) (R : β → S → ℕ → Prop)
    (x : Unit) :
    Triple ((chooseWith dispatch c).verifyWith m Q e)
      (fun s b ↦ 0 < b ∧ Q (fun r ↦ R r (e.act dispatch s) (b - 1)) (monadLift c : m β)) R x := by
  constructor
  rintro s b ⟨hb, h⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.mpr hb
  refine Syntax.ExecWithinWith.choice _ _ s b ?_
  rw [LawfulFunctorLiftT.monadLift_map, Q.map_iff]
  exact Q.mono (fun r hr ↦ .ret (v := .value) _ _ b
    (by simpa only [Equiv.symm_apply_apply])) h

section ChooseReturns

variable [MonadReturns m]

/-- Under `MonadQuant.all`, the continuation of a choice runs from every choice, which the
postcondition records. -/
@[spec]
theorem spec_chooseAct_all {d : ℕ} (c : F (A × Fin d))
    (e : Semantics O A Op Ret S) (s : S) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((chooseAct c).verifyWith m .all e) (fun t q ↦ t = s ∧ q = b)
      (fun j t q ↦ ∃ a, (a, j) ∈ returns (monadLift c : m (A × Fin d)) ∧
        t = e.act a s ∧ q = b - 1) x := by
  constructor
  rintro t q ⟨rfl, rfl⟩
  exact (spec_chooseAct c e _ x).le_wp t q ⟨h, fun r hr ↦ ⟨r.1, hr, rfl, rfl⟩⟩

/-- Under `MonadQuant.all`, the continuation of a choice runs from every value, which the
postcondition records. -/
@[spec]
theorem spec_chooseWith_all [Functor F] [LawfulMonad m] [LawfulFunctorLiftT F m] {β : Type}
    [FinEnum β] (dispatch : A) (c : F β)
    (e : Semantics O A Op Ret S) (s : S) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((chooseWith dispatch c).verifyWith m .all e) (fun t q ↦ t = s ∧ q = b)
      (fun r t q ↦ r ∈ returns (monadLift c : m β) ∧ t = e.act dispatch s ∧ q = b - 1) x := by
  constructor
  rintro t q ⟨rfl, rfl⟩
  exact (spec_chooseWith dispatch c e _ x).le_wp t q ⟨h, fun r hr ↦ ⟨hr, rfl, rfl⟩⟩

/-- Under `MonadQuant.any`, the continuation of a choice runs from a supplied choice. Not
registered: the caller chooses `(a, j)`. -/
theorem spec_chooseAct_any {d : ℕ} (c : F (A × Fin d))
    (e : Semantics O A Op Ret S) (a : A) (j : Fin d)
    (hj : (a, j) ∈ returns (monadLift c : m (A × Fin d))) (s : S) (b : ℕ) (h : 0 < b)
    (x : Unit) :
    Triple ((chooseAct c).verifyWith m .any e) (fun t q ↦ t = s ∧ q = b)
      (fun i t q ↦ i = j ∧ t = e.act a s ∧ q = b - 1) x := by
  constructor
  rintro t q ⟨rfl, rfl⟩
  exact (spec_chooseAct c e _ x).le_wp t q ⟨h, (a, j), hj, rfl, rfl, rfl⟩

/-- Under `MonadQuant.any`, the continuation of a choice runs from a supplied value. Not
registered: the caller chooses `v`. -/
theorem spec_chooseWith_any [Functor F] [LawfulMonad m] [LawfulFunctorLiftT F m] {β : Type}
    [FinEnum β] (dispatch : A) (c : F β)
    (e : Semantics O A Op Ret S) (v : β) (hv : v ∈ returns (monadLift c : m β)) (s : S) (b : ℕ)
    (h : 0 < b) (x : Unit) :
    Triple ((chooseWith dispatch c).verifyWith m .any e) (fun t q ↦ t = s ∧ q = b)
      (fun r t q ↦ r = v ∧ t = e.act dispatch s ∧ q = b - 1) x := by
  constructor
  rintro t q ⟨rfl, rfl⟩
  exact (spec_chooseWith dispatch c e _ x).le_wp t q ⟨h, v, hv, rfl, rfl, rfl⟩

end ChooseReturns

end Complexity.Program
