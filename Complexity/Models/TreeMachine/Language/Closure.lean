/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Data.FinEnum

/-! # Closing automatically allocated source variables

Only the variables occurring in a procedure need storage. Bounding their names turns a
procedure with natural-number variable names into one over a finite type.
-/

@[expose] public section

namespace Complexity.TreeProgram

namespace Expr

/-- An exclusive bound on the variable names occurring in an expression. -/
def bound : Expr ℕ → ℕ
  | .nil => 0
  | .var x => x + 1
  | .left e | .right e => e.bound
  | .pair a b => max a.bound b.bound

/-- Restrict variable names to a finite type containing every occurrence. -/
def close (e : Expr ℕ) (n : ℕ) (h : e.bound ≤ n) : Expr (Fin n) :=
  match e with
  | .nil => .nil
  | .var x => .var ⟨x, by change x + 1 ≤ n at h; omega⟩
  | .left e => .left (e.close n h)
  | .right e => .right (e.close n h)
  | .pair a b => .pair (a.close n (by simp only [bound] at h; omega))
      (b.close n (by simp only [bound] at h; omega))

@[simp] theorem eval_close (e : Expr ℕ) (n : ℕ) (h : e.bound ≤ n) (s : ℕ → Tree) :
    (e.close n h).eval (fun i ↦ s i.val) = e.eval s := by
  induction e with
  | nil | var => rfl
  | left e ih => exact congrArg BinaryTree.left (ih h)
  | right e ih => exact congrArg BinaryTree.right (ih h)
  | pair a b iha ihb => exact congrArg₂ Tree.pair (iha _) (ihb _)

@[simp] theorem maxSize_close (e : Expr ℕ) (n : ℕ) (h : e.bound ≤ n) (s : ℕ → Tree) :
    (e.close n h).maxSize (fun i ↦ s i.val) = e.maxSize s := by
  induction e with
  | nil | var => rfl
  | left e ih | right e ih => exact ih h
  | pair a b iha ihb => simp only [close, maxSize, eval_close, iha, ihb]

@[simp] theorem steps_close (e : Expr ℕ) (n : ℕ) (h : e.bound ≤ n) :
    (e.close n h).steps = e.steps := by
  induction e with
  | nil | var => rfl
  | left e ih | right e ih => exact congrArg (· + 1) (ih h)
  | pair a b iha ihb => simp only [close, steps, iha, ihb]

@[simp] theorem assignSteps_close (e : Expr ℕ) (n : ℕ) (h : e.bound ≤ n) :
    (e.close n h).assignSteps = e.assignSteps := by
  cases e with
  | nil | var => rfl
  | left e | right e => exact congrArg (· + 1) (steps_close e n h)
  | pair a b => simp only [close, assignSteps, steps_close]

end Expr

namespace Cmd

/-- An exclusive bound on all variable names read or written by a command. -/
def bound : Cmd ℕ → ℕ
  | .skip => 0
  | .assign x e => max (x + 1) e.bound
  | .seq p q => max p.bound q.bound
  | .branch e p q => max e.bound (max p.bound q.bound)
  | .while e p => max e.bound p.bound

/-- Restrict a command to a finite type containing every variable occurrence. -/
def close (p : Cmd ℕ) (n : ℕ) (h : p.bound ≤ n) : Cmd (Fin n) :=
  match p with
  | .skip => .skip
  | .assign x e => .assign ⟨x, by simp only [bound] at h; omega⟩
      (e.close n (by simp only [bound] at h; omega))
  | .seq p q => .seq (p.close n (by simp only [bound] at h; omega))
      (q.close n (by simp only [bound] at h; omega))
  | .branch e p q => .branch (e.close n (by simp only [bound] at h; omega))
      (p.close n (by simp only [bound] at h; omega))
      (q.close n (by simp only [bound] at h; omega))
  | .while e p => .while (e.close n (by simp only [bound] at h; omega))
      (p.close n (by simp only [bound] at h; omega))

/-- Execution depends only on the variables occurring in the command. -/
theorem Run.restrict {p : Cmd ℕ} {s t : ℕ → Tree} {time space : ℕ}
    (h : p.Run s time t space) (n : ℕ) (hn : p.bound ≤ n) :
    (p.close n hn).Run (fun i ↦ s i.val) time (fun i ↦ t i.val) space := by
  induction h with
  | skip s => exact .skip _
  | assign x e s =>
    rw [Function.update_comp_eq_of_injective' s Fin.val_injective
      ⟨x, by simp only [bound] at hn; omega⟩]
    have hh := Run.assign (ν := Fin n) ⟨x, by simp only [bound] at hn; omega⟩
      (e.close n (by simp only [bound] at hn; omega)) (fun i ↦ s i.val)
    simpa only [close, Expr.assignSteps_close, Expr.maxSize_close, Expr.eval_close] using hh
  | seq hp hq ihp ihq =>
    exact .seq (ihp (by simp only [bound] at hn; omega))
      (ihq (by simp only [bound] at hn; omega))
  | @branch_true e p q s t time size he hp ih =>
    have hh := Run.branch_true (e := e.close n (by simp only [bound] at hn; omega))
      (q := q.close n (by simp only [bound] at hn; omega))
      (by simpa using he) (ih (by simp only [bound] at hn; omega))
    simpa only [close, Expr.steps_close, Expr.maxSize_close] using hh
  | @branch_false e p q s t time size he hp ih =>
    have hh := Run.branch_false (e := e.close n (by simp only [bound] at hn; omega))
      (p := p.close n (by simp only [bound] at hn; omega))
      (by simpa using he) (ih (by simp only [bound] at hn; omega))
    simpa only [close, Expr.steps_close, Expr.maxSize_close] using hh
  | @while_false e p s he =>
    have hh := Run.while_false (e := e.close n (by simp only [bound] at hn; omega))
      (p := p.close n (by simp only [bound] at hn; omega))
      (s := fun i ↦ s i.val) (by simpa using he)
    simpa only [close, Expr.steps_close, Expr.maxSize_close] using hh
  | while_true he hp hr ihp ihr =>
    have hh := Run.while_true (by simpa using he)
      (ihp (by simp only [bound] at hn; omega)) (ihr hn)
    simpa only [close, Expr.steps_close, Expr.maxSize_close] using hh

theorem Exec.restrict {p : Cmd ℕ} {s t : ℕ → Tree} (h : p.Exec s t)
    (n : ℕ) (hn : p.bound ≤ n) :
    (p.close n hn).Exec (fun i ↦ s i.val) (fun i ↦ t i.val) := by
  obtain ⟨time, space, h⟩ := h
  exact ⟨time, space, h.restrict n hn⟩

end Cmd

namespace Procedure

/-- Enough variable names for the input, commands, and result. -/
def bound (p : Procedure ℕ) : ℕ :=
  max (p.input + 1) (max p.body.bound p.result.bound)

/-- A finite source procedure obtained without user-supplied variable enumeration. -/
def close (p : Procedure ℕ) : Procedure (Fin p.bound) where
  input := ⟨p.input, by simp only [bound]; omega⟩
  body := p.body.close p.bound (by simp only [bound]; omega)
  result := p.result.close p.bound (by simp only [bound]; omega)

theorem close_correct {p : Procedure ℕ} {x y : Tree} (h : p.Exec x y) :
    p.close.Exec x y := by
  obtain ⟨s, hs, hy⟩ := h
  refine ⟨fun i ↦ s i.val, ?_, ?_⟩
  · have h := hs.restrict p.bound (by simp only [bound]; omega)
    rw [Function.update_comp_eq_of_injective' _ Fin.val_injective
      ⟨p.input, show p.input < p.bound by simp only [bound]; omega⟩] at h
    exact h
  · simpa only [close, Expr.eval_close] using hy

theorem close_bounded {p : Procedure ℕ} {x y : Tree} {time space : ℕ}
    (h : p.Bounded x y time space) : p.close.Bounded x y time space := by
  obtain ⟨n, s, b, hr, hy, ht, hx, hb, hs⟩ := h
  refine ⟨n, fun i ↦ s i.val, b, ?_, ?_, ?_, hx, hb, ?_⟩
  · have h := hr.restrict p.bound (by simp only [bound]; omega)
    rw [Function.update_comp_eq_of_injective' _ Fin.val_injective
      ⟨p.input, show p.input < p.bound by simp only [bound]; omega⟩] at h
    exact h
  · simpa only [close, Expr.eval_close] using hy
  · simpa only [close, Expr.assignSteps_close] using ht
  · simpa only [close, Expr.maxSize_close] using hs

end Procedure
end Complexity.TreeProgram
