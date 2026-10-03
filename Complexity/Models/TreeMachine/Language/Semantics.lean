/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Basic

/-!
# Structured programs over tree values

Variables name source values, independently of the registers chosen by compilation.
Expressions read the old environment before an assignment updates its destination.
The terminating execution relation is a functional specification; it does not assign
unit cost to a whole expression or claim a resource bound for the compiled program.
-/

@[expose] public section

namespace Complexity.TreeProgram

/-- Tree expressions built from source variables. -/
inductive Expr (ν : Type) where
  | nil
  | var (x : ν)
  | left (e : Expr ν)
  | right (e : Expr ν)
  | pair (a b : Expr ν)
  deriving Repr

namespace Expr

variable {ν : Type}

/-- Evaluate an expression directly in the source environment. -/
def eval : Expr ν → (ν → Tree) → Tree
  | .nil, _ => .nil
  | .var x, s => s x
  | .left e, s => (e.eval s).left
  | .right e, s => (e.eval s).right
  | .pair a b, s => .pair (a.eval s) (b.eval s)

@[simp] theorem eval_nil (s : ν → Tree) : (nil : Expr ν).eval s = .nil := rfl

@[simp] theorem eval_var (x : ν) (s : ν → Tree) : (var x).eval s = s x := rfl

@[simp] theorem eval_left (e : Expr ν) (s : ν → Tree) :
    e.left.eval s = (e.eval s).left := rfl

@[simp] theorem eval_right (e : Expr ν) (s : ν → Tree) :
    e.right.eval s = (e.eval s).right := rfl

@[simp] theorem eval_pair (a b : Expr ν) (s : ν → Tree) :
    (pair a b).eval s = .pair (a.eval s) (b.eval s) := rfl

end Expr

/-- Assignment, sequencing, and structured control over source variables.
Tests select their true branch precisely when the evaluated tree is a node. -/
inductive Cmd (ν : Type) where
  | skip
  | assign (x : ν) (e : Expr ν)
  | seq (p q : Cmd ν)
  | branch (e : Expr ν) (yes no : Cmd ν)
  | while (e : Expr ν) (body : Cmd ν)
  deriving Repr

namespace Cmd

variable {ν : Type} [DecidableEq ν]

/-- A finite execution in source environments, with no reference to machine registers. -/
inductive Exec : Cmd ν → (ν → Tree) → (ν → Tree) → Prop where
  | skip (s : ν → Tree) : Exec .skip s s
  | assign (x : ν) (e : Expr ν) (s : ν → Tree) :
      Exec (.assign x e) s (Function.update s x (e.eval s))
  | seq {p q : Cmd ν} {s t u : ν → Tree}
      (hp : Exec p s t) (hq : Exec q t u) : Exec (.seq p q) s u
  | branch_true {e : Expr ν} {p q : Cmd ν} {s t : ν → Tree}
      (he : (e.eval s).root = true) (hp : Exec p s t) : Exec (.branch e p q) s t
  | branch_false {e : Expr ν} {p q : Cmd ν} {s t : ν → Tree}
      (he : (e.eval s).root = false) (hq : Exec q s t) : Exec (.branch e p q) s t
  | while_false {e : Expr ν} {p : Cmd ν} {s : ν → Tree}
      (he : (e.eval s).root = false) : Exec (.while e p) s s
  | while_true {e : Expr ν} {p : Cmd ν} {s t u : ν → Tree}
      (he : (e.eval s).root = true) (hp : Exec p s t) (hr : Exec (.while e p) t u) :
      Exec (.while e p) s u

@[simp] theorem exec_skip_iff {s t : ν → Tree} : Exec .skip s t ↔ t = s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .skip _

@[simp] theorem exec_assign_iff (x : ν) (e : Expr ν) {s t : ν → Tree} :
    Exec (.assign x e) s t ↔ t = Function.update s x (e.eval s) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .assign x e s

@[simp] theorem exec_seq_iff (p q : Cmd ν) {s t : ν → Tree} :
    Exec (.seq p q) s t ↔ ∃ u, Exec p s u ∧ Exec q u t := by
  constructor
  · intro h; cases h with | seq hp hq => exact ⟨_, hp, hq⟩
  · rintro ⟨u, hp, hq⟩; exact .seq hp hq

@[simp] theorem exec_branch_iff (e : Expr ν) (p q : Cmd ν) {s t : ν → Tree} :
    Exec (.branch e p q) s t ↔ if (e.eval s).root then Exec p s t else Exec q s t := by
  cases he : (e.eval s).root <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨fun h ↦ by cases h <;> simp_all, fun h ↦ .branch_false he h⟩
  · exact ⟨fun h ↦ by cases h <;> simp_all, fun h ↦ .branch_true he h⟩

/-- Source execution has a unique final environment whenever it terminates. -/
theorem Exec.deterministic {p : Cmd ν} {s t u : ν → Tree}
    (h : p.Exec s t) (h' : p.Exec s u) : t = u := by
  induction h generalizing u with
  | skip | assign => cases h'; rfl
  | seq hp hq ihp ihq =>
    cases h' with
    | seq hp' hq' => exact ihq (ihp hp' ▸ hq')
  | branch_true he hp ih =>
    cases h' with
    | branch_true _ hp' => exact ih hp'
    | branch_false he' _ => simp_all
  | branch_false he hp ih =>
    cases h' with
    | branch_true he' _ => simp_all
    | branch_false _ hp' => exact ih hp'
  | while_false he =>
    cases h' with
    | while_false => rfl
    | while_true he' _ _ => simp_all
  | while_true he hp hr ihp ihr =>
    cases h' with
    | while_false he' => simp_all
    | while_true _ hp' hr' => exact ihr (ihp hp' ▸ hr')

/-- Total correctness expressed entirely in terms of source variables and values. -/
def Total (p : Cmd ν) (P Q : (ν → Tree) → Prop) : Prop :=
  ∀ s, P s → ∃ t, p.Exec s t ∧ Q t

namespace Total

variable {p : Cmd ν}

/-- A source invariant and a decreasing natural measure prove loop termination. -/
theorem loop (e : Expr ν) (I : (ν → Tree) → Prop) (measure : (ν → Tree) → ℕ)
    (body : ∀ n, p.Total (fun s ↦ I s ∧ (e.eval s).root = true ∧ measure s = n)
      (fun t ↦ I t ∧ measure t < n)) :
    (Cmd.while e p).Total I (fun s ↦ I s ∧ (e.eval s).root = false) := by
  intro s hs
  generalize hn : measure s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    cases he : (e.eval s).root with
    | false => exact ⟨s, .while_false he, hs, he⟩
    | true =>
      obtain ⟨t, ht, hI, hv⟩ := body n s ⟨hs, he, hn⟩
      obtain ⟨u, hu, hQ⟩ := ih (measure t) hv t hI rfl
      exact ⟨u, .while_true he ht hu, hQ⟩

end Total
end Cmd

/-- A closed source procedure, with one tree input and one tree expression as its result. -/
structure Procedure (ν : Type) where
  /-- The variable initially containing the input tree. -/
  input : ν
  /-- The source statements, including local initializers. -/
  body : Cmd ν
  /-- The expression returned after the statements terminate. -/
  result : Expr ν

/-- Run a source procedure with every local variable initially empty. -/
def Procedure.Exec {ν : Type} [DecidableEq ν] (p : Procedure ν) (x y : Tree) : Prop :=
  ∃ s, p.body.Exec (Function.update (fun _ ↦ Tree.nil) p.input x) s ∧ p.result.eval s = y

end Complexity.TreeProgram
