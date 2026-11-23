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
`Syntax.ExecWithin` is the deterministic case, and an exact deterministic execution `Syntax.Exec`
is one whose budget is used up at its return.
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

end Within

variable {e : Semantics O A Op Ret S} {v w : Kind}

/-- Deterministic source executions within a budget: the run finishes within the budget and
returns a value satisfying the postcondition. -/
abbrev ExecWithin (e : Semantics O A Op Ret S) (p : Syntax Id O A Op Ret α v) (s : S) (b : ℕ)
    (R : Kind.Value α v → S → ℕ → Prop) : Prop :=
  p.ExecWithinWith Id .all e s b R

/-- Exact deterministic source execution: the run takes `n` transitions and returns `a` in the
state `t`. It is an execution within the budget `n` that uses up the budget at its return. -/
def Exec (e : Semantics O A Op Ret S) (p : Syntax Id O A Op Ret α v) (s : S) (n : ℕ)
    (a : Kind.Value α v) (t : S) : Prop :=
  p.ExecWithin e s n fun a' t' b ↦ a' = a ∧ t' = t ∧ b = 0

theorem Exec.ret (a : Kind.Value α v) (s : S) :
    Exec e (.ret a : Syntax Id O A Op Ret α v) s 0 a s :=
  ExecWithinWith.ret a s 0 ⟨rfl, rfl, rfl⟩

theorem Exec.step (o : Op) (k : Ret o → Syntax Id O A Op Ret α v) (s : S) {n : ℕ}
    {a : Kind.Value α v} {t : S}
    (h : Exec e (k (e.eval o (e.observe s)).2) (e.act (e.eval o (e.observe s)).1 s) n a t) :
    Exec e (.step o k) s (n + 1) a t :=
  ExecWithinWith.step o k s n h

/-- A deterministic choice node continues with its unique alternative, and charges one unit. -/
theorem Exec.choice {d : ℕ} (x : Id (A × Fin d)) (k : Fin d → Syntax Id O A Op Ret α v) (s : S)
    {n : ℕ} {a : Kind.Value α v} {t : S} (h : Exec e (k x.run.2) (e.act x.run.1 s) n a t) :
    Exec e (.choice x k) s (n + 1) a t :=
  ExecWithinWith.choice x k s n fun _ hr ↦ hr ▸ h

/-- Finishing a loop includes the charged dispatch before its last body. -/
theorem Exec.loop_done {n r : ℕ} (a : A) (i : Fin n)
    (body : Fin n → Syntax Id O A Op Ret α (.branch n r)) (k : Fin r → Syntax Id O A Op Ret α v)
    {s t u : S} {m l : ℕ} {j : Fin r} {x : Kind.Value α v}
    (hb : Exec e (body i) (e.act a s) m (.inr j) t) (hk : Exec e (k j) t l x u) :
    Exec e (.loop a i body k) s (m + l + 1) x u :=
  ExecWithinWith.loop a i body k s (m + l) (P := fun y t' b ↦ y = .inr j ∧ t' = t ∧ b = l)
    ((ExecWithinWith.add_budget hb l).mono fun _ _ _ ⟨_, ⟨hy, ht, hc⟩, hb⟩ ↦ ⟨hy, ht, by omega⟩)
    (fun _ _ _ h ↦ nomatch h.1) fun _ _ _ ⟨hy, ht, hb⟩ ↦ by cases hy; exact ht ▸ hb ▸ hk

/-- A continuing body routes directly to the next charged loop entry. -/
theorem Exec.loop_next {n r : ℕ} (a : A) (i : Fin n)
    (body : Fin n → Syntax Id O A Op Ret α (.branch n r)) (k : Fin r → Syntax Id O A Op Ret α v)
    {s t u : S} {m l : ℕ} {j : Fin n} {x : Kind.Value α v}
    (hb : Exec e (body i) (e.act a s) m (.inl j) t) (hk : Exec e (.loop a j body k) t l x u) :
    Exec e (.loop a i body k) s (m + l + 1) x u :=
  ExecWithinWith.loop a i body k s (m + l) (P := fun y t' b ↦ y = .inl j ∧ t' = t ∧ b = l)
    ((ExecWithinWith.add_budget hb l).mono fun _ _ _ ⟨_, ⟨hy, ht, hc⟩, hb⟩ ↦ ⟨hy, ht, by omega⟩)
    (fun _ _ _ ⟨hy, ht, hb⟩ ↦ by cases hy; exact ht ▸ hb ▸ hk) fun _ _ _ h ↦ nomatch h.1

/-- A call adds the exact cost of its block to that of its continuation. -/
theorem Exec.call {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax Id O A Op Ret α v) {s t u : S} {m l : ℕ} {j : Fin d}
    {x : Kind.Value α v}
    (hb : blk.RunWithin e.observe e.act (fun j' t' b ↦ j' = j ∧ t' = t ∧ b = 0) blk.start s m)
    (hk : Exec e (k j) t l x u) : Exec e (.call blk k) s (m + l) x u :=
  ExecWithinWith.call blk k <| (Control.RunWithinWith.add_budget hb l).mono
    fun _ _ _ ⟨_, ⟨hj, ht, hc⟩, hb⟩ ↦ by
      subst hj ht hc
      rw [hb, Nat.zero_add]
      exact hk

/-- Changing the outer return type leaves all actions and their costs unchanged. -/
theorem Exec.mapResult {p : Syntax Id O A Op Ret α v} {s t : S} {n : ℕ} {a : Kind.Value α v}
    (hp : Exec e p s n a t) (f : Kind.Value α v → Kind.Value β w) :
    Exec e (p.mapResult β w f) s n (f a) t :=
  (ExecWithinWith.mapResult hp f).mono fun _ _ _ ⟨_, hy, ha, ht, hb⟩ ↦ ⟨hy ▸ ha ▸ rfl, ht, hb⟩

/-- Substituting a continuation adds the two exact costs, with no connecting transition. -/
theorem Exec.bindTo {p : Syntax Id O A Op Ret α v} {f : Kind.Value α v → Syntax Id O A Op Ret β w}
    {s t u : S} {m n : ℕ} {a : Kind.Value α v} {b : Kind.Value β w}
    (hp : Exec e p s m a t) (hf : Exec e (f a) t n b u) : Exec e (p.bindTo f) s (m + n) b u :=
  (ExecWithinWith.add_budget hp n).bindTo fun _ _ _ ⟨_, ⟨ha, ht, hc⟩, hb⟩ ↦ by
    subst ha ht hc
    rw [hb, Nat.zero_add]
    exact hf

/-- An exact execution is an execution within any larger budget. -/
theorem Exec.execWithin {p : Syntax Id O A Op Ret α v} {s t : S} {n b : ℕ} {a : Kind.Value α v}
    {Q : Kind.Value α v → S → ℕ → Prop} (h : Exec e p s n a t) (hn : n ≤ b)
    (hQ : Q a t (b - n)) : p.ExecWithin e s b Q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (ExecWithinWith.add_budget h r).mono fun _ _ _ ⟨_, ⟨ha, ht, hc⟩, hb⟩ ↦ by
    subst ha ht hc hb
    simpa using hQ

/-- A deterministic execution within a budget contains an exact execution. -/
theorem ExecWithin.exists_exec {p : Syntax Id O A Op Ret α v} {s : S} {b : ℕ}
    {R : Kind.Value α v → S → ℕ → Prop} (h : p.ExecWithin e s b R) :
    ∃ n a t, n ≤ b ∧ Exec e p s n a t ∧ R a t (b - n) := by
  induction h with
  | ret a s b h => exact ⟨0, a, s, Nat.zero_le _, .ret a s, h⟩
  | step o k s b _ ih =>
    obtain ⟨n, a, t, hn, he, hR⟩ := ih
    exact ⟨n + 1, a, t, by omega, .step o k s he, by rwa [Nat.add_sub_add_right]⟩
  | choiceOn x k s b P hP _ ih =>
    obtain ⟨n, a, t, hn, he, hR⟩ := ih _ (hP _ rfl)
    exact ⟨n + 1, a, t, by omega, .choice x k s he, by rwa [Nat.add_sub_add_right]⟩
  | «loop» a i body k s b _ _ _ ihb ihn ihd =>
    obtain ⟨n₁, j | j, t₁, hn₁, he₁, hP⟩ := ihb
    · obtain ⟨n₂, a', u, hn₂, he₂, hR⟩ := ihn j t₁ _ hP
      exact ⟨n₁ + n₂ + 1, a', u, by omega, .loop_next a i body k he₁ he₂,
        by rwa [Nat.add_sub_add_right, ← Nat.sub_sub]⟩
    · obtain ⟨n₂, a', u, hn₂, he₂, hR⟩ := ihd j t₁ _ hP
      exact ⟨n₁ + n₂ + 1, a', u, by omega, .loop_done a i body k he₁ he₂,
        by rwa [Nat.add_sub_add_right, ← Nat.sub_sub]⟩
  | callOn blk k s b P hb _ ih =>
    obtain ⟨n₁, j, t, hn₁, hb, hk⟩ := Control.RunWithin.exists_exact hb
    obtain ⟨n₂, a, u, hn₂, he, hR⟩ := ih j t _ hk
    exact ⟨n₁ + n₂, a, u, by omega, .call blk k hb he, by rwa [Nat.sub_sub] at hR⟩

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

/-- Execute the source syntax with the chosen observation and action interpretation. -/
abbrev Exec (p : Program Id O A Op Ret α) (e : Semantics O A Op Ret S)
    (s : S) (n : ℕ) (a : α) (t : S) : Prop := Syntax.Exec e p s n a t

namespace Exec

variable {e : Semantics O A Op Ret S}

/-- Returning takes no action. -/
theorem pure (e : Semantics O A Op Ret S) (a : α) (s : S) :
    (Program.pure a : Program Id O A Op Ret α).Exec e s 0 a s := Syntax.Exec.ret (v := .value) a s

/-- A primitive performs exactly one action. -/
theorem perform (e : Semantics O A Op Ret S) (o : Op) (s : S) :
    (Program.perform (F := Id) o).Exec e s 1 (e.eval o (e.observe s)).2
      (e.act (e.eval o (e.observe s)).1 s) :=
  Syntax.Exec.step o (fun a ↦ Program.pure a) s (Syntax.Exec.ret _ _)

/-- Sequential composition adds costs without a connecting transition. -/
theorem bind {p : Program Id O A Op Ret α} {f : α → Program Id O A Op Ret β}
    {s t u : S} {m n : ℕ} {a : α} {b : β}
    (hp : p.Exec e s m a t) (hf : (f a).Exec e t n b u) :
    (p.bind f).Exec e s (m + n) b u := Syntax.Exec.bindTo hp hf

/-- Finishing a loop includes the charged dispatch before its last body. -/
theorem loop_done {n r : ℕ} (a : A)
    (body : Fin n → Program Id O A Op Ret (Fin n ⊕ Fin r))
    {i : Fin n} {j : Fin r} {s t : S} {m : ℕ}
    (h : (body i).Exec e (e.act a s) m (.inr j) t) :
    (loop a body i).Exec e s (m + 1) j t := by
  exact Syntax.Exec.loop_done a i _ _
    (by apply h.mapResult)
    (Syntax.Exec.ret (v := .value) j t)

/-- A continuing body routes directly to the next charged loop entry. -/
theorem loop_next {n r : ℕ} (a : A)
    (body : Fin n → Program Id O A Op Ret (Fin n ⊕ Fin r))
    {i j : Fin n} {s t u : S} {m l : ℕ} {v : Fin r}
    (h : (body i).Exec e (e.act a s) m (.inl j) t)
    (hc : (loop a body j).Exec e t l v u) :
    (loop a body i).Exec e s (m + l + 1) v u := by
  exact Syntax.Exec.loop_next a i _ _
    (by apply h.mapResult) hc

/-- A successful test terminates `repeatUntilWith` after its charged dispatch. -/
theorem repeatUntilWith_done (a : A) (p : Program Id O A Op Ret Bool) {s t : S} {m : ℕ}
    (h : p.Exec e (e.act a s) m true t) :
    (repeatUntilWith a p).Exec e s (m + 1) () t := by
  have hb := h.bind (f := fun b ↦ Program.pure
    (if b then Sum.inr (0 : Fin 1) else Sum.inl (0 : Fin 1))) (Exec.pure e
    (if true then Sum.inr (0 : Fin 1) else Sum.inl (0 : Fin 1)) t)
  have hl := loop_done a
    (fun _ : Fin 1 ↦ p.bind fun b ↦ Program.pure
      (if b then Sum.inr (0 : Fin 1) else Sum.inl (0 : Fin 1))) (i := 0) hb
  simpa only [repeatUntilWith, Bind.bind, Pure.pure, Nat.add_zero] using
    hl.bind (f := fun _ ↦ Program.pure ())
    (Exec.pure e () t)

/-- An unsuccessful test continues at the next charged dispatch. -/
theorem repeatUntilWith_next (a : A) (p : Program Id O A Op Ret Bool)
    {s t u : S} {m n : ℕ}
    (h : p.Exec e (e.act a s) m false t)
    (hc : (repeatUntilWith a p).Exec e t n () u) :
    (repeatUntilWith a p).Exec e s (m + n + 1) () u := by
  have hb := h.bind (f := fun b ↦ Program.pure
    (if b then Sum.inr (0 : Fin 1) else Sum.inl (0 : Fin 1)))
    (Exec.pure e (Sum.inl (0 : Fin 1)) t)
  apply Syntax.Exec.loop_next a 0 _ _
  · simpa only [repeatUntilWith, Bind.bind, Pure.pure, loop, bind, Syntax.bindTo,
      Syntax.mapResult_comp, Function.id_comp, Nat.add_zero, id_eq] using
      hb.mapResult (w := .branch 1 1) id
  · exact hc

end Exec
end Complexity.Program
