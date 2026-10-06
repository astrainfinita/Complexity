/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Language.Compiler
import Complexity.Models.TreeMachine.Language.Derive

open Complexity TreeProgram TreeProgram.Code

namespace Complexity.TreeDerivingTest

@[tree_encoding]
inductive Term (α : Type*) where
  | atom (a : α)
  | fork (left right : Term α)
  | empty

@[tree_encoding]
structure Record (α : Type*) where
  first : α
  second : Option Bool
  third : List α

@[tree_encoding]
structure Box (α : Type*) where
  value : α

@[tree_encoding]
inductive ImplicitField where
  | value {b : Bool}

@[tree_encoding]
inductive EmptyData

@[tree_encoding]
inductive UnitData where
  | unit

-- Existing field encodings compose, without extra delimiters on a fixed-arity payload.
example {α : Type*} [UniqueEncoding Tree α] (a : α) (b : Option Bool) (as : List α) :
    encode Tree (Record.mk a b as) =
      .pair (encode Tree a) (.pair (encode Tree b) (encode Tree as)) := by simp

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    encode Tree (Box.mk a) = encode Tree a := by simp

example (b : Bool) : encode Tree (@ImplicitField.value b) = encode Tree b := by simp

example : encode Tree UnitData.unit = .nil := by simp

example : decode EmptyData Tree.nil = Part.none := rfl
example : decode (Term Bool) Tree.nil = Part.none := rfl
example : decode (Term Bool) (Tree.pair .nil (.pair .nil (.pair .nil .nil))) = Part.none := by
  apply Part.eq_none_iff.mpr
  rintro (⟨(_ | _)⟩ | ⟨_, _⟩ | _) <;> simp [UniqueEncoding.mem_decode_iff]

-- The full inverse law rejects extra representations, not just roundtrips valid inputs.
example {α : Type*} [UniqueEncoding Tree α] (a : Term α) (t : Tree) :
    a ∈ decode (Term α) t ↔ encode Tree a = t := UniqueEncoding.mem_decode_iff

-- A source program is an ordinary definition; its specification is an ordinary Lean function.
def swapRoot (x : Value) : Code Value :=
  Term.Code.matchOn x
    Term.Code.atom
    (fun left right => Term.Code.fork right left)
    Term.Code.empty

def Term.swapRoot {α : Type*} : Term α → Term α
  | .atom a => .atom a
  | .fork left right => .fork right left
  | .empty => .empty

theorem swapRoot_correct {α : Type*} [UniqueEncoding Tree α] (x : Term α) :
    (swapRoot .input).Computes (encode Tree x) (encode Tree x.swapRoot) := by
  cases x <;> simp [computes_iff, swapRoot, Term.swapRoot]

-- The existing compiler transfers this source proof directly to a finite tree machine.
example {α : Type*} [UniqueEncoding Tree α] (x : Term α) :
    let p := swapRoot .input
    ∃ n, p.compile.Halted (p.compile.run (TreeMachine.Cfg p.registers _) (encode Tree x) n) ∧
      (p.compile.run (TreeMachine.Cfg p.registers _) (encode Tree x) n).regs 0 =
        encode Tree x.swapRoot :=
  Code.compile_correct (swapRoot_correct x)

-- Unit-returning cases work with mutable variables and unequal allocations in the branches.
def unwrapOrEmpty (x : Value) : Code Value := do
  let result ← newVar .nil
  Option.Code.casesOn x (pure ()) fun a => do
    let temp ← newVar a
    write result (← read temp)
  read result

example {α : Type*} [UniqueEncoding Tree α] (x : Option α) :
    (unwrapOrEmpty .input).Computes (encode Tree x)
      (x.elim Tree.nil (encode Tree)) := by
  cases x <;> simp [computes_iff, unwrapOrEmpty]

-- List keeps its existing compact format, including for non-Boolean element types.
def head? (xs : Value) : Code Value :=
  List.Code.matchOn xs Option.Code.none (fun a _ => Option.Code.some a)

example {α : Type*} [UniqueEncoding Tree α] (as : List α) :
    (head? .input).Computes (encode Tree as) (encode Tree as.head?) := by
  cases as <;> simp [computes_iff, head?]

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    (Box.Code.matchOn .input pure).Computes (encode Tree (Box.mk a)) (encode Tree a) := by
  simp [computes_iff]

-- A structure projection needs no runtime branching or result slot.
example (x : Value) (n : ℕ) : (Box.Code.matchOn x pure).build n = (x, n, []) := rfl

def extendRecord (x : Value) : Code Value :=
  Record.Code.matchOn x fun a b as => do Record.Code.mk a b (← List.Code.cons a as)

example {α : Type*} [UniqueEncoding Tree α] (r : Record α) :
    (extendRecord .input).Computes (encode Tree r)
      (encode Tree { r with third := r.first :: r.third }) := by
  cases r
  simp [computes_iff, extendRecord]

example (b : Bool) :
    (Bool.Code.matchOn .input Bool.Code.true Bool.Code.false).Computes
      (encode Tree b) (encode Tree (!b)) := by
  cases b <;> simp [computes_iff]

-- In particular, introducing generic List encoding has not changed the existing bit-list code.
example (as : List Bool) : encode Tree as = Tree.encodeBitList as := rfl

run_cmd do
  for name in [``Term.treeEncoding, ``Record.treeEncoding, ``Box.treeEncoding,
      ``ImplicitField.treeEncoding, ``EmptyData.treeEncoding, ``UnitData.treeEncoding] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on an unfinished proof"

section Rejection

/-- error: Complexity.TreeDerivingTest.Term already has a tree encoding; deriving would change its representation -/
#guard_msgs in
attribute [tree_encoding] Term

/-- error: List already has a tree encoding; deriving would change its representation -/
#guard_msgs in
attribute [tree_encoding] List

inductive Redundant where | value
instance : Encoding Tree Redundant where
  decode _ := pure .value
  exists_code a := by cases a; exact ⟨.nil, Part.mem_some _⟩

/-- error: Complexity.TreeDerivingTest.Redundant already has a tree encoding; deriving would change its representation -/
#guard_msgs in
attribute [tree_encoding] Redundant

inductive Indexed : Bool → Type where | value : Indexed true

/-- error: Tree encoding requires constructor result indices to be distinct fields -/
#guard_msgs in
attribute [tree_encoding] Indexed

inductive Nested where | node (xs : List Nested)

/-- error: Tree encoding currently supports non-nested, non-mutual first-order inductive types -/
#guard_msgs in
attribute [tree_encoding] Nested

inductive FunctionField where | mk (f : Bool → Bool)

/-- error: Tree encoding needs an instance of UniqueEncoding Tree (Bool → Bool) -/
#guard_msgs in
attribute [tree_encoding] FunctionField

structure DependentField where
  b : Bool
  value : if b then Bool else Tree

/-- error: Tree encoding needs an instance of UniqueEncoding Tree (if b = true then Bool else Tree) -/
#guard_msgs in
attribute [tree_encoding] DependentField

/-- error: Nat needs its binary encoding, not the default constructor encoding -/
#guard_msgs in
attribute [tree_encoding] Nat

end Rejection

end Complexity.TreeDerivingTest
