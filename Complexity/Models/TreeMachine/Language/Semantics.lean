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
The same terminating execution records expression costs; functional specifications simply
forget those measurements. Compilation relates them to unit time and peak tree space.
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

/-- Largest source tree encountered during expression evaluation, including discarded subtrees. -/
@[simp] def maxSize : Expr ν → (ν → Tree) → ℕ
  | .nil, _ => 1
  | .var x, s => (s x).size
  | .left e, s | .right e, s => e.maxSize s
  | .pair a b, s => max (a.maxSize s) (max (b.maxSize s) (Tree.pair (a.eval s) (b.eval s)).size)

/-- The returned tree is one of the values covered by the source bound. -/
theorem size_eval_le_maxSize (e : Expr ν) (s : ν → Tree) :
    (e.eval s).size ≤ e.maxSize s := by
  induction e with
  | nil | var => exact Nat.le_refl _
  | left e ih => exact Nat.le_trans (Tree.size_left_le _) ih
  | right e ih => exact Nat.le_trans (Tree.size_right_le _) ih
  | pair a b => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- An expression building a constant tree. -/
def ofTree : Tree → Expr ν
  | .nil => .nil
  | .node _ l r => .pair (ofTree l) (ofTree r)

@[simp] theorem eval_ofTree (T : Tree) (s : ν → Tree) : (ofTree T).eval s = T := by
  induction T with
  | nil => rfl
  | node _ l r hl hr => simp only [ofTree, eval_pair, hl, hr]

@[simp] theorem maxSize_ofTree (T : Tree) (s : ν → Tree) : (ofTree T).maxSize s = T.size := by
  induction T with
  | nil => rfl
  | node _ l r hl hr =>
    simp only [ofTree, maxSize, hl, hr, eval_ofTree]
    change max (Tree.size l) (max (Tree.size r) (Tree.pair l r).size) = (Tree.pair l r).size
    simp only [Tree.size_pair]; omega

/-- Exact unit time for obtaining an expression's value; existing values need no copy. -/
@[simp] def steps : Expr ν → ℕ
  | .nil | .var _ => 0
  | .left e | .right e => e.steps + 1
  | .pair a b => a.steps + (b.steps + 1)

/-- Exact unit time when the expression is assigned to a source variable. -/
def assignSteps : Expr ν → ℕ
  | .nil => 1
  | .var _ => 2
  | .left e | .right e => e.steps + 1
  | .pair a b => a.steps + (b.steps + 1)

attribute [simp] assignSteps.eq_1 assignSteps.eq_2 assignSteps.eq_3
  assignSteps.eq_4 assignSteps.eq_5

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

/-- A source execution records its exact compiled unit time and the largest evaluated
subexpression. Initial values and the compiler's copy overhead are added at the boundary. -/
inductive Run : Cmd ν → (ν → Tree) → ℕ → (ν → Tree) → ℕ → Prop where
  | skip (s : ν → Tree) : Run .skip s 0 s 0
  | assign (x : ν) (e : Expr ν) (s : ν → Tree) :
      Run (.assign x e) s e.assignSteps (Function.update s x (e.eval s)) (e.maxSize s)
  | seq {p q : Cmd ν} {s t u : ν → Tree} {n m a b : ℕ}
      (hp : Run p s n t a) (hq : Run q t m u b) : Run (.seq p q) s (n + m) u (max a b)
  | branch_true {e : Expr ν} {p q : Cmd ν} {s t : ν → Tree} {n a : ℕ}
      (he : (e.eval s).root = true) (hp : Run p s n t a) :
      Run (.branch e p q) s (e.steps + 1 + n) t (max (e.maxSize s) a)
  | branch_false {e : Expr ν} {p q : Cmd ν} {s t : ν → Tree} {n a : ℕ}
      (he : (e.eval s).root = false) (hq : Run q s n t a) :
      Run (.branch e p q) s (e.steps + 1 + n) t (max (e.maxSize s) a)
  | while_false {e : Expr ν} {p : Cmd ν} {s : ν → Tree}
      (he : (e.eval s).root = false) : Run (.while e p) s (e.steps + 2) s (e.maxSize s)
  | while_true {e : Expr ν} {p : Cmd ν} {s t u : ν → Tree} {n m a b : ℕ}
      (he : (e.eval s).root = true) (hp : Run p s n t a) (hr : Run (.while e p) t m u b) :
      Run (.while e p) s (e.steps + 2 + n + m) u (max (e.maxSize s) (max a b))

/-- Functional execution forgets the resource measurements of the same source run. -/
def Exec (p : Cmd ν) (s t : ν → Tree) : Prop := ∃ n b, p.Run s n t b

/-- Bounding the initial values and all evaluated expressions bounds the final environment. -/
theorem Run.size_le {p : Cmd ν} {s t : ν → Tree} {n b space : ℕ}
    (h : p.Run s n t b) (hs : ∀ i, (s i).size ≤ space) (hb : b ≤ space) :
    ∀ i, (t i).size ≤ space := by
  induction h with
  | skip | while_false => exact hs
  | assign x e s =>
    intro i
    by_cases hi : i = x
    · simpa [hi] using Nat.le_trans (e.size_eval_le_maxSize s) hb
    · simpa [Function.update_of_ne hi] using hs i
  | seq hp hq ihp ihq => exact ihq (ihp hs (by omega)) (by omega)
  | branch_true he hp ih | branch_false he hp ih => exact ih hs (by omega)
  | while_true he hp hr ihp ihr => exact ihr (ihp hs (by omega)) (by omega)

namespace Exec

variable {p q : Cmd ν} {e : Expr ν} {s t u : ν → Tree}

theorem skip (s : ν → Tree) : Exec .skip s s := ⟨_, _, .skip s⟩

theorem assign (x : ν) (e : Expr ν) (s : ν → Tree) :
    Exec (.assign x e) s (Function.update s x (e.eval s)) := ⟨_, _, .assign x e s⟩

theorem seq (hp : p.Exec s t) (hq : q.Exec t u) : (Cmd.seq p q).Exec s u := by
  obtain ⟨_, _, hp⟩ := hp
  obtain ⟨_, _, hq⟩ := hq
  exact ⟨_, _, .seq hp hq⟩

theorem branch_true (he : (e.eval s).root = true) (hp : p.Exec s t) :
    (Cmd.branch e p q).Exec s t := by
  obtain ⟨_, _, hp⟩ := hp
  exact ⟨_, _, .branch_true he hp⟩

theorem branch_false (he : (e.eval s).root = false) (hq : q.Exec s t) :
    (Cmd.branch e p q).Exec s t := by
  obtain ⟨_, _, hq⟩ := hq
  exact ⟨_, _, .branch_false he hq⟩

theorem while_false (he : (e.eval s).root = false) : (Cmd.while e p).Exec s s :=
  ⟨_, _, .while_false he⟩

theorem while_true (he : (e.eval s).root = true) (hp : p.Exec s t)
    (hr : (Cmd.while e p).Exec t u) : (Cmd.while e p).Exec s u := by
  obtain ⟨_, _, hp⟩ := hp
  obtain ⟨_, _, hr⟩ := hr
  exact ⟨_, _, .while_true he hp hr⟩

end Exec

@[simp] theorem exec_skip_iff {s t : ν → Tree} : Exec .skip s t ↔ t = s := by
  constructor
  · rintro ⟨_, _, h⟩; cases h; rfl
  · rintro rfl; exact .skip _

@[simp] theorem exec_assign_iff (x : ν) (e : Expr ν) {s t : ν → Tree} :
    Exec (.assign x e) s t ↔ t = Function.update s x (e.eval s) := by
  constructor
  · rintro ⟨_, _, h⟩; cases h; rfl
  · rintro rfl; exact .assign x e s

@[simp] theorem exec_seq_iff (p q : Cmd ν) {s t : ν → Tree} :
    Exec (.seq p q) s t ↔ ∃ u, Exec p s u ∧ Exec q u t := by
  constructor
  · rintro ⟨_, _, h⟩; cases h with | seq hp hq => exact ⟨_, ⟨_, _, hp⟩, ⟨_, _, hq⟩⟩
  · rintro ⟨u, hp, hq⟩; exact .seq hp hq

@[simp] theorem exec_branch_iff (e : Expr ν) (p q : Cmd ν) {s t : ν → Tree} :
    Exec (.branch e p q) s t ↔ if (e.eval s).root then Exec p s t else Exec q s t := by
  cases he : (e.eval s).root <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨fun ⟨_, _, h⟩ ↦ by cases h <;> first | exact ⟨_, _, ‹_›⟩ | simp_all,
      fun h ↦ .branch_false he h⟩
  · exact ⟨fun ⟨_, _, h⟩ ↦ by cases h <;> first | exact ⟨_, _, ‹_›⟩ | simp_all,
      fun h ↦ .branch_true he h⟩

/-- Source execution has a unique final environment whenever it terminates. -/
theorem Run.deterministic {p : Cmd ν} {s t u : ν → Tree} {n m a b : ℕ}
    (h : p.Run s n t a) (h' : p.Run s m u b) : t = u := by
  induction h generalizing m u b with
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

theorem Exec.deterministic {p : Cmd ν} {s t u : ν → Tree}
    (h : p.Exec s t) (h' : p.Exec s u) : t = u := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h'⟩ := h'
  exact h.deterministic h'

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

/-- Source budgets include input, evaluated subexpressions and the returned expression.
Compilation turns the tree-size bound into a register-mass bound with a static factor. -/
def Procedure.Bounded {ν : Type} [DecidableEq ν] (p : Procedure ν)
    (x y : Tree) (time space : ℕ) : Prop :=
  ∃ n s b, p.body.Run (Function.update (fun _ ↦ Tree.nil) p.input x) n s b ∧
    p.result.eval s = y ∧ 2 + (n + p.result.assignSteps) ≤ time ∧
    x.size ≤ space ∧ b ≤ space ∧ p.result.maxSize s ≤ space

end Complexity.TreeProgram
