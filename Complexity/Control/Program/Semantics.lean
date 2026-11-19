/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Syntax

/-! # Exact executions of source programs -/

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

/-- Exact terminating source execution. A loop dispatch costs one step; calls add no wrapper
step. The result type is an index, allowing a loop body to return its own finite control sum.
There is no rule for a choice node: these executions are those of deterministic programs, and of
the parts of other programs that pass no choice. -/
inductive Exec (e : Semantics O A Op Ret S) :
    {α : Type} → {v : Kind} → Syntax F O A Op Ret α v → S → ℕ → Kind.Value α v → S → Prop where
  | ret {α : Type} {v : Kind} (a : Kind.Value α v) (s : S) : Exec e (.ret a) s 0 a s
  | step {α : Type} {v : Kind} (o : Op) (k : Ret o → Syntax F O A Op Ret α v) (s : S)
      {m : ℕ} {a : Kind.Value α v} {t : S}
      (h : Exec e (k (e.eval o (e.observe s)).2)
        (e.act (e.eval o (e.observe s)).1 s) m a t) :
      Exec e (.step o k) s (m + 1) a t
  | loop_done {α : Type} {v : Kind} {n r : ℕ} (a : A) (i : Fin n)
      (body : Fin n → Syntax F O A Op Ret α (.branch n r))
      (k : Fin r → Syntax F O A Op Ret α v)
      {s t u : S} {m l : ℕ} {j : Fin r} {x : Kind.Value α v}
      (hb : Exec e (body i) (e.act a s) m (.inr j) t)
      (hk : Exec e (k j) t l x u) : Exec e (.loop a i body k) s (m + l + 1) x u
  | loop_next {α : Type} {v : Kind} {n r : ℕ} (a : A) (i : Fin n)
      (body : Fin n → Syntax F O A Op Ret α (.branch n r))
      (k : Fin r → Syntax F O A Op Ret α v)
      {s t u : S} {m l : ℕ} {j : Fin n} {x : Kind.Value α v}
      (hb : Exec e (body i) (e.act a s) m (.inl j) t)
      (hk : Exec e (.loop a j body k) t l x u) :
      Exec e (.loop a i body k) s (m + l + 1) x u
  | call {α : Type} {v : Kind} {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
      (k : Fin d → Syntax F O A Op Ret α v)
      {s t u : S} {m l : ℕ} {j : Fin d} {x : Kind.Value α v}
      (hb : Control.Run b id e.observe e.act b.start s m j t) (hk : Exec e (k j) t l x u) :
      Exec e (.call b k) s (m + l) x u

/-- Changing the outer return type leaves all actions and their costs unchanged. -/
theorem Exec.mapResult {e : Semantics O A Op Ret S} {v w : Kind}
    {p : Syntax F O A Op Ret α v} {s t : S} {m : ℕ} {a : Kind.Value α v}
    (hp : Exec e p s m a t) (f : Kind.Value α v → Kind.Value β w) :
    Exec e (p.mapResult β w f) s m (f a) t := by
  induction hp generalizing β w with
  | ret a s => exact .ret (f a) s
  | step o k s h ih => exact .step o _ s (ih f)
  | loop_done a i body k hb hk ihb ihk =>
    exact .loop_done a i _ _ (by apply ihb) (ihk f)
  | loop_next a i body k hb hk ihb ihk =>
    exact .loop_next a i _ _ (by apply ihb) (ihk f)
  | call b k hb hk ih => exact .call b _ hb (ih f)

/-- Substituting a continuation adds the two exact costs, with no connecting transition. -/
theorem Exec.bindTo {e : Semantics O A Op Ret S} {v w : Kind}
    {p : Syntax F O A Op Ret α v} {f : Kind.Value α v → Syntax F O A Op Ret β w}
    {s t u : S} {m n : ℕ} {a : Kind.Value α v} {b : Kind.Value β w}
    (hp : Exec e p s m a t) (hf : Exec e (f a) t n b u) :
    Exec e (p.bindTo f) s (m + n) b u := by
  induction hp generalizing β w with
  | ret a s => simpa only [bindTo, Nat.zero_add] using hf
  | step o k s h ih =>
    convert Exec.step o (fun x ↦ bindTo (k x) f) s (ih hf) using 1 <;>
      first | rfl | omega
  | loop_done a i body k hb hk _ ih =>
    convert Exec.loop_done a i
      (fun j ↦ (body j).mapResult β (.branch _ _) id) (fun x ↦ bindTo (k x) f)
      (by apply hb.mapResult)
      (ih hf) using 1 <;> first | rfl | omega
  | loop_next a i body k hb hk _ ih =>
    convert Exec.loop_next a i
      (fun j ↦ (body j).mapResult β (.branch _ _) id) (fun x ↦ bindTo (k x) f)
      (by apply hb.mapResult)
      (ih hf) using 1 <;> first | rfl | omega
  | call block k hb hk ih =>
    convert Exec.call block (fun x ↦ bindTo (k x) f) hb (ih hf) using 1 <;>
      first | rfl | omega

end Syntax


/-- Execute the source syntax with the chosen observation and action interpretation. -/
abbrev Exec (p : Program F O A Op Ret α) (e : Semantics O A Op Ret S)
    (s : S) (n : ℕ) (a : α) (t : S) : Prop := Syntax.Exec e p s n a t

namespace Exec

variable {e : Semantics O A Op Ret S}

/-- Returning takes no action. -/
theorem pure (e : Semantics O A Op Ret S) (a : α) (s : S) :
    (Program.pure (F := F) a).Exec e s 0 a s := Syntax.Exec.ret (v := .value) a s

/-- A primitive performs exactly one action. -/
theorem perform (e : Semantics O A Op Ret S) (o : Op) (s : S) :
    (Program.perform (F := F) o).Exec e s 1 (e.eval o (e.observe s)).2
      (e.act (e.eval o (e.observe s)).1 s) :=
  Syntax.Exec.step o (fun a ↦ Program.pure a) s (Syntax.Exec.ret _ _)

/-- Sequential composition adds costs without a connecting transition. -/
theorem bind {p : Program F O A Op Ret α} {f : α → Program F O A Op Ret β}
    {s t u : S} {m n : ℕ} {a : α} {b : β}
    (hp : p.Exec e s m a t) (hf : (f a).Exec e t n b u) :
    (p.bind f).Exec e s (m + n) b u := Syntax.Exec.bindTo hp hf

/-- Finishing a loop includes the charged dispatch before its last body. -/
theorem loop_done {n r : ℕ} (a : A)
    (body : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    {i : Fin n} {j : Fin r} {s t : S} {m : ℕ}
    (h : (body i).Exec e (e.act a s) m (.inr j) t) :
    (loop a body i).Exec e s (m + 1) j t := by
  exact Syntax.Exec.loop_done a i _ _
    (by apply h.mapResult)
    (Syntax.Exec.ret (v := .value) j t)

/-- A continuing body routes directly to the next charged loop entry. -/
theorem loop_next {n r : ℕ} (a : A)
    (body : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    {i j : Fin n} {s t u : S} {m l : ℕ} {v : Fin r}
    (h : (body i).Exec e (e.act a s) m (.inl j) t)
    (hc : (loop a body j).Exec e t l v u) :
    (loop a body i).Exec e s (m + l + 1) v u := by
  exact Syntax.Exec.loop_next a i _ _
    (by apply h.mapResult) hc

/-- A successful test terminates `repeatUntilWith` after its charged dispatch. -/
theorem repeatUntilWith_done (a : A) (p : Program F O A Op Ret Bool) {s t : S} {m : ℕ}
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
theorem repeatUntilWith_next (a : A) (p : Program F O A Op Ret Bool)
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
