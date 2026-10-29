/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Code

/-! # Source proof rules for monadic tree programs -/

@[expose] public section

namespace Complexity.TreeProgram.Code

variable {α β : Type} {n m l : ℕ} {s t u : ℕ → Tree} {unitResult : Unit}

@[simp] theorem exec_block_nil : (block []).Exec s t ↔ t = s := by
  simp [block]

@[simp] theorem exec_block_cons (c : Cmd ℕ) (cs : List (Cmd ℕ)) :
    (block (c :: cs)).Exec s t ↔ ∃ u, c.Exec s u ∧ (block cs).Exec u t := by
  simp [block]

@[simp] theorem exec_block_append (cs ds : List (Cmd ℕ)) :
    (block (cs ++ ds)).Exec s t ↔ ∃ u, (block cs).Exec s u ∧ (block ds).Exec u t := by
  induction cs generalizing s with
  | nil => simp
  | cons c cs ih => simp only [List.cons_append, exec_block_cons, ih]; aesop

@[simp] theorem exec_pure_iff (a b : α) :
    (pure a : Code α).Exec n s b m t ↔ b = a ∧ m = n ∧ t = s := by
  simp [Exec, eq_comm, and_assoc]

@[simp] theorem exec_bind_iff (p : Code α) (f : α → Code β) (b : β) :
    (p >>= f).Exec n s b l t ↔ ∃ a m u, p.Exec n s a m u ∧ (f a).Exec m u b l t := by
  simp [Exec, Prod.ext_iff]
  aesop

@[simp] theorem exec_map_iff (f : α → β) (p : Code α) (b : β) :
    (f <$> p).Exec n s b m t ↔ ∃ a, p.Exec n s a m t ∧ b = f a := by
  simp only [map_eq_pure_bind, exec_bind_iff, exec_pure_iff]
  aesop

namespace Exec

variable {p : Code α} {f : α → Code β} {a : α} {b : β}

theorem pure (a : α) : (Pure.pure a : Code α).Exec n s a n s := by simp

theorem bind (hp : p.Exec n s a m u) (hf : (f a).Exec m u b l t) :
    (p >>= f).Exec n s b l t := exec_bind_iff p f b |>.mpr ⟨a, m, u, hp, hf⟩

theorem result (h : p.Exec n s a m t) : (p.build n).1 = a := congrArg Prod.fst h.1

theorem counter (h : p.Exec n s a m t) : (p.build n).2.1 = m :=
  congrArg (fun x ↦ x.2.1) h.1

end Exec

@[simp] theorem exec_emit_iff (c : Cmd ℕ) :
    (emit c).Exec n s unitResult m t ↔ m = n ∧ c.Exec s t := by
  simp [Exec, eq_comm]

@[simp] theorem exec_newVar_iff (v : Value) (a : Var) :
    (newVar v).Exec n s a m t ↔
      a = ⟨n⟩ ∧ m = n + 1 ∧ t = Function.update s n (v.eval s) := by
  simp [Exec, eq_comm, and_assoc]

@[simp] theorem exec_eval_iff (e : Expr ℕ) (a : Value) :
    (eval e).Exec n s a m t ↔
      a = .var n ∧ m = n + 1 ∧ t = Function.update s n (e.eval s) := by
  simp [Exec, eq_comm, and_assoc]

@[simp] theorem exec_read_iff (v : Var) (a : Value) :
    (read v).Exec n s a m t ↔
      a = .var n ∧ m = n + 1 ∧ t = Function.update s n (v.get s) := by
  simp [read, Var.get]

@[simp] theorem exec_write_iff (v : Var) (a : Value) :
    (write v a).Exec n s unitResult m t ↔
      m = n ∧ t = Function.update s v.index (a.eval s) := by
  simp [Exec, eq_comm]

@[simp] theorem exec_ifNode_iff (v : Value) (yes no : Code Unit) :
    (ifNode v yes no).Exec n s unitResult m t ↔
      m = max (yes.build n).2.1 (no.build n).2.1 ∧
      if (v.eval s).root then yes.Exec n s () (yes.build n).2.1 t
      else no.Exec n s () (no.build n).2.1 t := by
  cases he : (v.eval s).root <;> simp [Exec, Prod.ext_iff, he, eq_comm]

@[simp] theorem exec_branch_iff (e : Expr ℕ) (yes no : Code Value) (a : Value) :
    (branch e yes no).Exec n s a m t ↔
      a = .var n ∧ m = max (yes.build (n + 1)).2.1 (no.build (n + 1)).2.1 ∧
      let p := if (e.eval s).root then yes else no
      (p >>= fun v ↦ write ⟨n⟩ v).Exec (n + 1) s () (p.build (n + 1)).2.1 t := by
  cases h : (e.eval s).root <;> simp [Exec, Prod.ext_iff, h, eq_comm, and_assoc]

namespace Exec

theorem whileNode_false (v : Var) (body : Code Unit) (h : (v.get s).root = false) :
    (whileNode v body).Exec n s () (body.build n).2.1 s := by
  refine ⟨rfl, ?_⟩
  simpa using (Cmd.Exec.while_false (e := Expr.var v.index) h : _)

theorem whileNode_true (v : Var) (body : Code Unit) (h : (v.get s).root = true)
    (hb : body.Exec n s () m u) (hr : (whileNode v body).Exec n u () m t) :
    (whileNode v body).Exec n s () m t := by
  refine ⟨hr.1, ?_⟩
  simpa using Cmd.Exec.while_true (e := .var v.index) h hb.2 (by simpa using hr.2)

end Exec

/-- Total correctness of source code. Postconditions refer to source values and locations. -/
def Total (p : Code α) (n : ℕ) (P : (ℕ → Tree) → Prop)
    (Q : α → (ℕ → Tree) → Prop) : Prop :=
  ∀ s, P s → ∃ a m t, p.Exec n s a m t ∧ Q a t

@[simp] theorem total_pure_iff (a : α) (P : (ℕ → Tree) → Prop)
    (Q : α → (ℕ → Tree) → Prop) :
    (pure a : Code α).Total n P Q ↔ ∀ s, P s → Q a s := by
  simp [Total]

@[simp] theorem total_newVar_iff (v : Value) (P : (ℕ → Tree) → Prop)
    (Q : Var → (ℕ → Tree) → Prop) :
    (newVar v).Total n P Q ↔ ∀ s, P s → Q ⟨n⟩ (Function.update s n (v.eval s)) := by
  simp [Total]

@[simp] theorem total_eval_iff (e : Expr ℕ) (P : (ℕ → Tree) → Prop)
    (Q : Value → (ℕ → Tree) → Prop) :
    (eval e).Total n P Q ↔ ∀ s, P s → Q (.var n) (Function.update s n (e.eval s)) := by
  simp [Total]

@[simp] theorem total_read_iff (v : Var) (P : (ℕ → Tree) → Prop)
    (Q : Value → (ℕ → Tree) → Prop) :
    (read v).Total n P Q ↔ ∀ s, P s → Q (.var n) (Function.update s n (v.get s)) := by
  simp [Total]

@[simp] theorem total_write_iff (v : Var) (a : Value) (P : (ℕ → Tree) → Prop)
    (Q : Unit → (ℕ → Tree) → Prop) :
    (write v a).Total n P Q ↔ ∀ s, P s → Q () (Function.update s v.index (a.eval s)) := by
  simp [Total, Unique.exists_iff]

namespace Total

variable {p : Code α} {f : α → Code β} {P P' : (ℕ → Tree) → Prop}
    {Q Q' : α → (ℕ → Tree) → Prop} {R : β → (ℕ → Tree) → Prop}

theorem consequence (h : p.Total n P Q) (hp : ∀ s, P' s → P s)
    (hq : ∀ a s, Q a s → Q' a s) : p.Total n P' Q' := by
  intro s hs
  obtain ⟨a, m, t, ht, hQ⟩ := h s (hp s hs)
  exact ⟨a, m, t, ht, hq a t hQ⟩

theorem pure (a : α) (Q : α → (ℕ → Tree) → Prop) :
    (Pure.pure a : Code α).Total n (Q a) Q :=
  fun s hs ↦ ⟨a, n, s, Exec.pure a, hs⟩

theorem bind (hp : p.Total n P Q)
    (hf : ∀ a, (f a).Total (p.build n).2.1 (Q a) R) : (p >>= f).Total n P R := by
  intro s hs
  obtain ⟨a, m, u, hp', hQ⟩ := hp s hs
  obtain ⟨b, l, t, hf', hR⟩ := hf a u hQ
  rw [hp'.counter] at hf'
  exact ⟨b, l, t, hp'.bind hf', hR⟩

theorem newVar (v : Value) (Q : Var → (ℕ → Tree) → Prop) :
    (Code.newVar v).Total n (fun s ↦ Q ⟨n⟩ (Function.update s n (v.eval s))) Q :=
  fun s hs ↦ ⟨⟨n⟩, n + 1, _, by simp, hs⟩

theorem read (v : Var) (Q : Value → (ℕ → Tree) → Prop) :
    (Code.read v).Total n (fun s ↦ Q (.var n) (Function.update s n (v.get s))) Q :=
  fun s hs ↦ ⟨.var n, n + 1, _, by simp, hs⟩

theorem write (v : Var) (a : Value) (Q : (ℕ → Tree) → Prop) :
    (Code.write v a).Total n (fun s ↦ Q (Function.update s v.index (a.eval s)))
      (fun _ ↦ Q) := fun s hs ↦ ⟨(), n, _, by simp, hs⟩

theorem ifNode (v : Value) (yes no : Code Unit) (Q : Unit → (ℕ → Tree) → Prop)
    (hy : yes.Total n (fun s ↦ P s ∧ (v.eval s).root = true) Q)
    (hn : no.Total n (fun s ↦ P s ∧ (v.eval s).root = false) Q) :
    (Code.ifNode v yes no).Total n P Q := by
  intro s hs
  cases he : (v.eval s).root with
  | false =>
    obtain ⟨⟨⟩, m, t, ht, hQ⟩ := hn s ⟨hs, he⟩
    exact ⟨(), _, t, (exec_ifNode_iff ..).mpr ⟨rfl, by simpa [he, ht.counter] using ht⟩, hQ⟩
  | true =>
    obtain ⟨⟨⟩, m, t, ht, hQ⟩ := hy s ⟨hs, he⟩
    exact ⟨(), _, t, (exec_ifNode_iff ..).mpr ⟨rfl, by simpa [he, ht.counter] using ht⟩, hQ⟩

/-- An invariant and decreasing source measure prove termination of a monadic loop. -/
theorem whileNode (v : Var) (body : Code Unit) (I : (ℕ → Tree) → Prop)
    (measure : (ℕ → Tree) → ℕ)
    (hb : ∀ k, body.Total n (fun s ↦ I s ∧ (v.get s).root = true ∧ measure s = k)
      (fun _ t ↦ I t ∧ measure t < k)) :
    (Code.whileNode v body).Total n I (fun _ s ↦ I s ∧ (v.get s).root = false) := by
  have hbody : ∀ k, (block (body.build n).2.2).Total
      (fun s ↦ I s ∧ (v.get s).root = true ∧ measure s = k)
      (fun t ↦ I t ∧ measure t < k) := by
    intro k s hs
    obtain ⟨a, m, t, ht, hQ⟩ := hb k s hs
    exact ⟨t, ht.2, hQ⟩
  intro s hs
  obtain ⟨t, ht, hQ⟩ := Cmd.Total.loop (.var v.index) I measure hbody s hs
  exact ⟨(), (body.build n).2.1, t, ⟨rfl, by simpa using ht⟩, hQ⟩

end Total

/-- Close a source execution with the usual input environment and evaluate its returned value. -/
theorem computes_iff (p : Code Value) (x y : Tree) :
    p.Computes x y ↔ ∃ a m t,
      p.Exec 1 (Function.update (fun _ ↦ Tree.nil) 0 x) a m t ∧ a.eval t = y := by
  simp [Computes, source, Procedure.Exec, Exec, Prod.ext_iff]

/-- A closed source contract suffices to establish the input/output specification. -/
theorem Total.computes {p : Code Value} {P : (ℕ → Tree) → Prop} {x y : Tree}
    (h : p.Total 1 P (fun a t ↦ a.eval t = y))
    (hp : P (Function.update (fun _ ↦ Tree.nil) 0 x)) : p.Computes x y :=
  (computes_iff p x y).mpr (h _ hp)

end Complexity.TreeProgram.Code
