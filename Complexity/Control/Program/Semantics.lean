/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.MonadReturns
public import Complexity.Control.Program.Syntax

/-! # Executions of source programs

A specification fixes the interpretation of the operations of a program (`Semantics`), the
interpretation `m` of its choices and a quantifier `Q : MonadQuant m` reading the choices.
`Syntax.ExecWithinWith m Q` is an inductive predicate: an operation, a loop dispatch and a choice
charge one unit of the budget, a choice continues from a set of choices the quantifier accepts, the
results of a loop body continue at the next dispatch or after the loop, and a call runs its block
within the budget (`Control.RunWithin`). For `MonadQuant.all`, every run finishes
within the budget and returns a value satisfying the postcondition; for `MonadQuant.any`, some run
does. A run that has not finished when the budget is spent satisfies nothing.
`Syntax.ExecWithin` is the deterministic case.
-/

@[expose] public section

namespace Complexity.Program

/-- Fix the interpretation only when specifying a source program. -/
structure Semantics (O A Op : Type) (Ret : Op → Type) (S : Type) where
  /-- Evaluate a recorded operation at the current observation. -/
  eval : (o : Op) → O → A × Ret o
  /-- Read the local observation from the semantic state. -/
  observe : S → O
  /-- Apply one local action to the semantic state. -/
  act : A → S → S

variable {F : Type → Type} {O A Op S α β : Type} {Ret : Op → Type}

namespace Syntax

section Within

/-- Source executions within a budget whose outcomes the quantifier `Q` reads, the choices
interpreted in `m`: for `MonadQuant.all`, every run finishes within the budget and returns a value
satisfying the postcondition, for `MonadQuant.any` some run does. An operation, a loop dispatch
and a choice charge one unit and calls add no wrapper step, as in the compiled controller. The
result type is an index, allowing a loop body to return its own finite control sum. A choice and a
call continue from a set `P` of results named in the derivation: choices that the quantifier
accepts, and exits that the block reaches within the budget. -/
inductive ExecWithinWith (m : Type → Type) [Monad m] [MonadLiftT F m] (Q : MonadQuant m)
    (e : Semantics O A Op Ret S) :
    {v : Kind} → Syntax F O A Op Ret α v → S → ℕ → (Kind.Value α v → S → ℕ → Prop) → Prop where
  | ret {v : Kind} (a : Kind.Value α v) (s : S) (b : ℕ) {R : Kind.Value α v → S → ℕ → Prop}
      (hR : R a s b) : ExecWithinWith m Q e (.ret a) s b R
  | step {v : Kind} (o : Op) (k : Ret o → Syntax F O A Op Ret α v) (s : S) (b : ℕ)
      {R : Kind.Value α v → S → ℕ → Prop}
      (h : ExecWithinWith m Q e (k (e.eval o (e.observe s)).2) (e.act (e.eval o (e.observe s)).1 s)
        b R) :
      ExecWithinWith m Q e (.step o k) s (b + 1) R
  /-- A choice charges one unit and continues from a set of choices that the quantifier accepts. -/
  | choiceOn {v : Kind} {d : ℕ} (x : F (A × Fin d)) (k : Fin d → Syntax F O A Op Ret α v) (s : S)
      (b : ℕ) {R : Kind.Value α v → S → ℕ → Prop} (P : A × Fin d → Prop)
      (hP : Q P (monadLift x : m (A × Fin d)))
      (h : ∀ r, P r → ExecWithinWith m Q e (k r.2) (e.act r.1 s) b R) :
      ExecWithinWith m Q e (.choice x k) s (b + 1) R
  /-- The results of the body continue at the next entry or after the loop. -/
  | loop {v : Kind} {n r : ℕ} (a : A) (i : Fin n)
      (body : Fin n → Syntax F O A Op Ret α (.branch n r)) (k : Fin r → Syntax F O A Op Ret α v)
      (s : S) (b : ℕ) {P : Fin n ⊕ Fin r → S → ℕ → Prop} {R : Kind.Value α v → S → ℕ → Prop}
      (hb : ExecWithinWith m Q e (body i) (e.act a s) b P)
      (hnext : ∀ j t b', P (.inl j) t b' → ExecWithinWith m Q e (.loop a j body k) t b' R)
      (hdone : ∀ j t b', P (.inr j) t b' → ExecWithinWith m Q e (k j) t b' R) :
      ExecWithinWith m Q e (.loop a i body k) s (b + 1) R
  /-- A call runs its block within the budget, without a wrapper step, and continues from a set of
  exits that the block reaches. -/
  | callOn {v : Kind} {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
      (k : Fin d → Syntax F O A Op Ret α v) (s : S) (b : ℕ) {R : Kind.Value α v → S → ℕ → Prop}
      (P : Fin d → S → ℕ → Prop) (hb : blk.RunWithin e.observe e.act P blk.start s b)
      (hk : ∀ j t b', P j t b' → ExecWithinWith m Q e (k j) t b' R) :
      ExecWithinWith m Q e (.call blk k) s b R

variable {m : Type → Type} [Monad m] [MonadLiftT F m] {Q : MonadQuant m}
  {e : Semantics O A Op Ret S} {v w : Kind}

theorem execWithinWith_ret_iff {a : Kind.Value α v} {s : S} {b : ℕ}
    {R : Kind.Value α v → S → ℕ → Prop} :
    (Syntax.ret a : Syntax F O A Op Ret α v).ExecWithinWith m Q e s b R ↔ R a s b :=
  ⟨fun h ↦ by cases h; assumption, .ret a s b⟩

/-- An operation charges one unit and continues with the result of its evaluation. -/
theorem execWithinWith_step_iff {o : Op} {k : Ret o → Syntax F O A Op Ret α v} {s : S} {b : ℕ}
    {R : Kind.Value α v → S → ℕ → Prop} :
    (Syntax.step o k).ExecWithinWith m Q e s b R ↔ 0 < b ∧
      (k (e.eval o (e.observe s)).2).ExecWithinWith m Q e (e.act (e.eval o (e.observe s)).1 s)
        (b - 1) R := by
  refine ⟨fun h ↦ ?_, fun ⟨hb, h⟩ ↦ ?_⟩
  · cases h with | step _ _ _ b h => exact ⟨b.succ_pos, h⟩
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.2 hb
    exact .step o k s b h

/-- A choice charges one unit, and the quantifier reads the continuation over the choices. -/
theorem execWithinWith_choice_iff {d : ℕ} {x : F (A × Fin d)}
    {k : Fin d → Syntax F O A Op Ret α v} {s : S} {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop} :
    (Syntax.choice x k).ExecWithinWith m Q e s b R ↔ 0 < b ∧
      Q (fun r ↦ (k r.2).ExecWithinWith m Q e (e.act r.1 s) (b - 1) R)
        (monadLift x : m (A × Fin d)) := by
  refine ⟨fun h ↦ ?_, fun ⟨hb, h⟩ ↦ ?_⟩
  · cases h with | choiceOn _ _ _ b P hP h => exact ⟨b.succ_pos, Q.mono h hP⟩
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.2 hb
    exact .choiceOn x k s b _ h fun _ hr ↦ hr

/-- A call runs its block within the budget, without a wrapper step, and continues at the block's
exit with the remaining budget. -/
theorem execWithinWith_call_iff {c d : ℕ} {blk : Control Id O A (Fin c) (Fin d)}
    {k : Fin d → Syntax F O A Op Ret α v} {s : S} {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop} :
    (Syntax.call blk k).ExecWithinWith m Q e s b R ↔
      blk.RunWithin e.observe e.act (fun j t b' ↦ (k j).ExecWithinWith m Q e t b' R)
        blk.start s b :=
  ⟨fun h ↦ by cases h with | callOn _ _ _ _ P hb hk => exact hb.mono hk,
    fun h ↦ .callOn blk k s b _ h fun _ _ _ h ↦ h⟩

/-- A weaker postcondition holds of the same executions. -/
theorem ExecWithinWith.mono {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ}
    {P R : Kind.Value α v → S → ℕ → Prop} (hp : p.ExecWithinWith m Q e s b P)
    (hPR : ∀ a t b', P a t b' → R a t b') : p.ExecWithinWith m Q e s b R := by
  induction hp with
  | ret a s b h => exact .ret a s b (hPR _ _ _ h)
  | step o k s b _ ih => exact .step o k s b (ih hPR)
  | choiceOn x k s b P hP _ ih => exact .choiceOn x k s b P hP fun r hr ↦ ih r hr hPR
  | «loop» a i body k s b hb _ _ _ ihn ihd =>
    exact .loop a i body k s b hb (fun j t b' h ↦ ihn j t b' h hPR) fun j t b' h ↦ ihd j t b' h hPR
  | callOn blk k s b P hb _ ih => exact .callOn blk k s b P hb fun j t b' h ↦ ih j t b' h hPR

/-- An invariant indexed by the remaining budget, preserved by every action that costs one unit,
holds at every return. -/
theorem ExecWithinWith.inv {I : S → ℕ → Prop} (hI : ∀ a s b, I s (b + 1) → I (e.act a s) b)
    {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop}
    (h : p.ExecWithinWith m Q e s b R) (hs : I s b) :
    p.ExecWithinWith m Q e s b (fun a t b' ↦ R a t b' ∧ I t b') := by
  induction h with
  | ret a s b h => exact .ret a s b ⟨h, hs⟩
  | step o k s b _ ih => exact .step o k s b (ih (hI _ s b hs))
  | choiceOn x k s b P hP _ ih => exact .choiceOn x k s b P hP fun r hr ↦ ih r hr (hI r.1 s b hs)
  | «loop» a i body k s b _ _ _ ihb ihn ihd =>
    exact .loop a i body k s b (ihb (hI a s b hs)) (fun j t b' h ↦ ihn j t b' h.1 h.2)
      fun j t b' h ↦ ihd j t b' h.1 h.2
  | callOn blk k s b P hb _ ih =>
    exact .callOn blk k s b _ (Control.RunWithinWith.inv hI hb hs) fun j t b' h ↦ ih j t b' h.1 h.2

/-- The remaining budget never exceeds the initial one. -/
theorem ExecWithinWith.with_le {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ}
    {R : Kind.Value α v → S → ℕ → Prop} (hp : p.ExecWithinWith m Q e s b R) :
    p.ExecWithinWith m Q e s b (fun a t b' ↦ b' ≤ b ∧ R a t b') :=
  (hp.inv (I := fun _ b' ↦ b' ≤ b) (fun _ _ _ h ↦ by omega) le_rfl).mono
    fun _ _ _ ⟨hR, hb⟩ ↦ ⟨hb, hR⟩

/-- A loop dispatch charges one unit, and the results of the body continue at the next dispatch
or after the loop. -/
theorem execWithinWith_loop_iff {n r : ℕ} {a : A} {i : Fin n}
    {body : Fin n → Syntax F O A Op Ret α (.branch n r)} {k : Fin r → Syntax F O A Op Ret α v}
    {s : S} {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop} :
    (Syntax.loop a i body k).ExecWithinWith m Q e s b R ↔ 0 < b ∧
      (body i).ExecWithinWith m Q e (e.act a s) (b - 1) fun y t b' ↦ match y with
        | .inl j => (Syntax.loop a j body k).ExecWithinWith m Q e t b' R
        | .inr j => (k j).ExecWithinWith m Q e t b' R := by
  refine ⟨fun h ↦ ?_, fun ⟨hb, h⟩ ↦ ?_⟩
  · cases h with
    | «loop» _ _ _ _ _ b hb hn hd =>
      exact ⟨b.succ_pos, hb.mono fun y t b' hy ↦ by
        rcases y with j | j
        exacts [hn j t b' hy, hd j t b' hy]⟩
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.2 hb
    exact .loop a i body k s b h (fun _ _ _ h ↦ h) fun _ _ _ h ↦ h

/-- A choice charges one unit, and the quantifier reads the continuation over the choices. -/
theorem ExecWithinWith.choice {d : ℕ}
    (x : F (A × Fin d)) (k : Fin d → Syntax F O A Op Ret α v) (s : S) (b : ℕ)
    {R : Kind.Value α v → S → ℕ → Prop}
    (h : Q (fun r ↦ (k r.2).ExecWithinWith m Q e (e.act r.1 s) b R) (monadLift x : m (A × Fin d))) :
    (Syntax.choice x k).ExecWithinWith m Q e s (b + 1) R :=
  .choiceOn x k s b _ h fun _ hr ↦ hr

/-- A call runs its block within the budget, without a wrapper step, and continues at the block's
exit. -/
theorem ExecWithinWith.call {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α v) {s : S} {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop}
    (h : blk.RunWithin e.observe e.act (fun j t b' ↦ (k j).ExecWithinWith m Q e t b' R)
      blk.start s b) :
    (Syntax.call blk k).ExecWithinWith m Q e s b R :=
  .callOn blk k s b _ h fun _ _ _ h ↦ h

/-- Changing the outer return type leaves all actions, choices and their costs unchanged. -/
theorem ExecWithinWith.mapResult {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ}
    {P : Kind.Value α v → S → ℕ → Prop} (hp : p.ExecWithinWith m Q e s b P)
    (f : Kind.Value α v → Kind.Value β w) :
    (p.mapResult β w f).ExecWithinWith m Q e s b (fun y t b' ↦ ∃ a, f a = y ∧ P a t b') := by
  induction hp generalizing β w with
  | ret a s b h => exact .ret _ s b ⟨a, rfl, h⟩
  | step o k s b _ ih => exact .step o _ s b (ih f)
  | choiceOn x k s b P hP _ ih => exact .choiceOn x _ s b P hP fun r hr ↦ ih r hr f
  | «loop» a i body k s b _ _ _ ihb ihn ihd =>
    refine .loop a i _ _ s b (ihb (β := β) (w := .branch _ _) id) ?_ ?_
    · rintro j t b' ⟨_, rfl, h⟩
      exact ihn j t b' h f
    · rintro j t b' ⟨_, rfl, h⟩
      exact ihd j t b' h f
  | callOn blk k s b P hb _ ih => exact .callOn blk _ s b P hb fun j t b' h ↦ ih j t b' h f

/-- Substituting a continuation runs it from every return of the first execution, with no
connecting transition. -/
theorem ExecWithinWith.bindTo {p : Syntax F O A Op Ret α v}
    {f : Kind.Value α v → Syntax F O A Op Ret β w} {s : S} {b : ℕ}
    {P : Kind.Value α v → S → ℕ → Prop} {R : Kind.Value β w → S → ℕ → Prop}
    (hp : p.ExecWithinWith m Q e s b P)
    (hf : ∀ a t b', P a t b' → (f a).ExecWithinWith m Q e t b' R) :
    (p.bindTo f).ExecWithinWith m Q e s b R := by
  induction hp with
  | ret a s b h => exact hf a s b h
  | step o k s b _ ih => exact .step o _ s b (ih hf)
  | choiceOn x k s b P hP _ ih => exact .choiceOn x _ s b P hP fun r hr ↦ ih r hr hf
  | «loop» a i body k s b hb _ _ _ ihn ihd =>
    refine .loop a i _ _ s b (hb.mapResult (β := β) (w := .branch _ _) id) ?_ ?_
    · rintro j t b' ⟨_, rfl, h⟩
      exact ihn j t b' h hf
    · rintro j t b' ⟨_, rfl, h⟩
      exact ihd j t b' h hf
  | callOn blk k s b P hb _ ih => exact .callOn blk _ s b P hb fun j t b' h ↦ ih j t b' h hf

/-- Extra budget passes through an execution unused. -/
theorem ExecWithinWith.add_budget {p : Syntax F O A Op Ret α v} {s : S} {b : ℕ}
    {R : Kind.Value α v → S → ℕ → Prop} (hp : p.ExecWithinWith m Q e s b R) (r : ℕ) :
    p.ExecWithinWith m Q e s (b + r) (fun a t b' ↦ ∃ c, R a t c ∧ b' = c + r) := by
  induction hp with
  | ret a s b h => exact .ret a s _ ⟨b, h, rfl⟩
  | step o k s b _ ih => exact Nat.add_right_comm b 1 r ▸ .step o k s (b + r) ih
  | choiceOn x k s b P hP _ ih => exact Nat.add_right_comm b 1 r ▸ .choiceOn x k s (b + r) P hP ih
  | «loop» a i body k s b _ _ _ ihb ihn ihd =>
    refine Nat.add_right_comm b 1 r ▸ .loop a i body k s (b + r) ihb ?_ ?_
    · rintro j t _ ⟨c, h, rfl⟩
      exact ihn j t c h
    · rintro j t _ ⟨c, h, rfl⟩
      exact ihd j t c h
  | callOn blk k s b P hb _ ih =>
    refine .callOn blk k s (b + r) _ (hb.add_budget r) ?_
    rintro j t _ ⟨c, h, rfl⟩
    exact ih j t c h

/-- A larger budget allows the same execution, when the postcondition does not read the remaining
budget. -/
theorem ExecWithinWith.mono_budget {p : Syntax F O A Op Ret α v} {s : S} {b b' : ℕ}
    {P : Kind.Value α v → S → Prop} (hp : p.ExecWithinWith m Q e s b fun a t _ ↦ P a t)
    (hb : b ≤ b') : p.ExecWithinWith m Q e s b' fun a t _ ↦ P a t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hb
  exact (hp.add_budget r).mono fun _ _ _ ⟨_, h, _⟩ ↦ h

/-- Budgets add along a continuation. -/
theorem ExecWithinWith.bindTo_add {p : Syntax F O A Op Ret α v}
    {f : Kind.Value α v → Syntax F O A Op Ret β w} {s : S} {b c : ℕ}
    {P : Kind.Value α v → S → Prop} {R : Kind.Value β w → S → Prop}
    (hp : p.ExecWithinWith m Q e s b fun a t _ ↦ P a t)
    (hf : ∀ a t, P a t → (f a).ExecWithinWith m Q e t c fun x u _ ↦ R x u) :
    (p.bindTo f).ExecWithinWith m Q e s (b + c) fun x u _ ↦ R x u :=
  (hp.add_budget c).bindTo fun a t _ ⟨d, hP, hd⟩ ↦
    hd ▸ (hf a t hP).mono_budget (Nat.le_add_left c d)

end Within

variable {e : Semantics O A Op Ret S} {v : Kind}

/-- Deterministic source executions within a budget: the run finishes within the budget and
returns a value satisfying the postcondition. -/
abbrev ExecWithin (e : Semantics O A Op Ret S) (p : Syntax Id O A Op Ret α v) (s : S) (b : ℕ)
    (R : Kind.Value α v → S → ℕ → Prop) : Prop :=
  p.ExecWithinWith Id .all e s b R

/-- A deterministic execution within a budget is one of the embedding by `ofId` into any choice
shape, under any interpretation of the choices and any quantifier reading the lift of
`Pure.pure a` as `a`. -/
theorem ExecWithin.ofId [Pure F] {m : Type → Type} [Monad m] [MonadLiftT F m]
    {Q : MonadQuant m} [MonadQuant.PureLiftT F m Q] {p : Syntax Id O A Op Ret α v} {s : S}
    {b : ℕ} {R : Kind.Value α v → S → ℕ → Prop} (h : p.ExecWithin e s b R) :
    (p.ofId (F := F)).ExecWithinWith m Q e s b R := by
  induction h with
  | ret a s b h => exact .ret a s b h
  | step o k s b _ ih => exact .step o _ s b ih
  | choiceOn x k s b P hP _ ih => exact .choice _ _ s b (Q.monadLift_pure_iff.2 (ih _ (hP _ rfl)))
  | «loop» a i body k s b _ _ _ ihb ihn ihd => exact .loop a i _ _ s b ihb ihn ihd
  | callOn blk k s b P hb _ ih => exact .callOn blk _ s b P hb ih

end Syntax

end Complexity.Program
