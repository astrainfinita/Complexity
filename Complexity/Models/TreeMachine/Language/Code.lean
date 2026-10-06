/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Semantics
public import Mathlib.Control.Basic

/-! # Tree programs constructed by ordinary Lean definitions

`Code` is a construction monad. Its variables are source locations, not physical registers.
Reads create snapshots, and tree operations bind their computed results to fresh source
variables. Branch and loop combinators construct their bodies once, before machine execution.
-/

@[expose] public section

namespace Complexity.TreeProgram

/-- An immutable source value: the empty tree or an already computed source variable. -/
inductive Value where
  | nil
  | var (index : ℕ)

/-- A mutable source location, allocated independently of the target register layout. -/
@[ext] structure Var where
  /-- The symbolic identity of this source location. -/
  index : ℕ
  deriving DecidableEq

namespace Value

/-- The source expression referencing this value, without repeating its computation. -/
def expression : Value → Expr ℕ
  | .nil => .nil
  | .var i => .var i

attribute [simp] expression.eq_1 expression.eq_2

/-- Interpret a value in a source environment. -/
def eval : Value → (ℕ → Tree) → Tree
  | .nil, _ => .nil
  | .var i, s => s i

/-- The input value, available before any local allocations. -/
def input : Value := .var 0

@[simp] theorem eval_expression (v : Value) (s : ℕ → Tree) :
    v.expression.eval s = v.eval s := by cases v <;> rfl

@[simp] theorem eval_input (s : ℕ → Tree) : input.eval s = s 0 := rfl
@[simp] theorem eval_nil (s : ℕ → Tree) : nil.eval s = .nil := rfl
@[simp] theorem eval_var (i : ℕ) (s : ℕ → Tree) : (var i).eval s = s i := rfl

end Value

/-- Read a mutable source location when stating a source specification. -/
def Var.get (v : Var) (s : ℕ → Tree) : Tree := s v.index

@[simp] theorem Var.get_mk (i : ℕ) (s : ℕ → Tree) : (Var.mk i).get s = s i := rfl

/-- A construction produces a result, a fresh-name supply, and source statements. -/
@[ext] structure Code (α : Type) where
  /-- Construct source statements; the counter is unrelated to target registers. -/
  build : ℕ → α × ℕ × List (Cmd ℕ)

namespace Code

variable {α β : Type}

instance : Monad Code where
  pure a := ⟨fun n ↦ (a, n, [])⟩
  bind p f := ⟨fun n ↦
    let (a, m, cs) := p.build n
    let (b, l, ds) := (f a).build m
    (b, l, cs ++ ds)⟩

@[simp] theorem build_pure (a : α) (n : ℕ) :
    (pure a : Code α).build n = (a, n, []) := rfl

@[simp] theorem build_bind (p : Code α) (f : α → Code β) (n : ℕ) :
    (p >>= f).build n =
      let (a, m, cs) := p.build n
      let (b, l, ds) := (f a).build m
      (b, l, cs ++ ds) := rfl

instance : LawfulMonad Code := LawfulMonad.mk' _
  (fun p ↦ by
    apply Code.ext
    funext n
    change (p >>= fun a ↦ pure a).build n = p.build n
    simp only [build_bind, build_pure, List.append_nil])
  (fun a f ↦ by
    apply Code.ext
    funext n
    simp only [build_bind, build_pure, List.nil_append])
  (fun p f g ↦ by
    apply Code.ext
    funext n
    simp only [build_bind, List.append_assoc])

/-- Combine the source statements emitted by a construction. -/
def block : List (Cmd ℕ) → Cmd ℕ
  | [] => .skip
  | c :: cs => .seq c (block cs)

/-- Emit a source statement without allocating a variable. -/
@[simps build]
def emit (c : Cmd ℕ) : Code Unit := ⟨fun n ↦ ((), n, [c])⟩

/-- Allocate and initialize a mutable source variable. -/
@[simps build]
def newVar (v : Value) : Code Var :=
  ⟨fun n ↦ (⟨n⟩, n + 1, [.assign n v.expression])⟩

/-- Evaluate a source expression once and retain its result as an immutable value. -/
@[simps build]
def eval (e : Expr ℕ) : Code Value :=
  ⟨fun n ↦ (.var n, n + 1, [.assign n e])⟩

/-- Read a mutable location into a fresh immutable snapshot. -/
@[simps! build]
def read (v : Var) : Code Value := eval (.var v.index)

/-- Assign a tree value to a mutable source location. -/
@[simps! build]
def write (v : Var) (x : Value) : Code Unit := emit (.assign v.index x.expression)

/-- Select a source block by a value's root. Exclusive branches share local slots. -/
@[simps build]
def ifNode (v : Value) (yes no : Code Unit) : Code Unit := ⟨fun n ↦
  let (_, m, cs) := yes.build n
  let (_, l, ds) := no.build n
  ((), max m l, [.branch v.expression (block cs) (block ds)])⟩

/-- Recheck the mutable variable's root each iteration. The body is constructed only once. -/
@[simps build]
def whileNode (v : Var) (body : Code Unit) : Code Unit := ⟨fun n ↦
  let (_, m, cs) := body.build n
  ((), m, [.while (.var v.index) (block cs)])⟩

/-- Source execution of a monadic construction, independently of machine compilation. -/
def Exec (p : Code α) (n : ℕ) (s : ℕ → Tree) (a : α) (m : ℕ) (t : ℕ → Tree) : Prop :=
  p.build n = (a, m, (p.build n).2.2) ∧ (block (p.build n).2.2).Exec s t

/-- A closed program starts with its input and builds locals after that symbolic location. -/
def source (p : Code Value) : Procedure ℕ :=
  { input := 0, body := block (p.build 1).2.2, result := (p.build 1).1.expression }

/-- The result of the source program on a tree input. -/
def Computes (p : Code Value) (x y : Tree) : Prop := p.source.Exec x y

end Code

namespace Value

/-- Compute the left subtree once. -/
@[simp] def left (v : Value) : Code Value := Code.eval (.left v.expression)

/-- Compute the right subtree once. -/
@[simp] def right (v : Value) : Code Value := Code.eval (.right v.expression)

/-- Construct a node once, retaining its result for subsequent uses. -/
@[simp] def pair (a b : Value) : Code Value := Code.eval (.pair a.expression b.expression)

end Value

end Complexity.TreeProgram
