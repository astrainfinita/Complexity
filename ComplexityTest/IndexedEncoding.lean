/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Encoding.Sigma
import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding

namespace IndexedEncodingTest

-- Deriving outside `Complexity` requires no open namespace or encoding notation.
@[tree_encoding]
inductive Fixed : Bool → Type where
  | value : Fixed true

@[tree_encoding]
inductive Mixed (α : Type*) : ℕ → Bool → Type _ where
  | fixed (a : α) : Mixed α 2 true
  | general {n : ℕ} (a : α) : Mixed α n false

@[tree_encoding]
inductive SingletonIndex : Unit → Type where
  | mk (b : Bool) : SingletonIndex ()

@[tree_encoding]
inductive Recursive : Bool → Type where
  | atom (b : Bool) : Recursive false
  | lift (x : Recursive false) : Recursive true
  | join {b : Bool} (x y : Recursive b) : Recursive b

open Complexity TreeProgram TreeProgram.Code FirstOrder

example : decode (Fixed false) Complexity.Tree.nil = Part.none := rfl

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    decode (Mixed α 1 true) (encode Tree (Mixed.fixed a)) = Part.none := rfl

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    encode Tree (Mixed.fixed a) = encode Tree ((), a) := by simp

example {b : Bool} (x : Recursive b) : decode (Recursive b) (encode Tree x) = Part.some x :=
  UniqueEncoding.decode_encode x

example (b : Bool) : encode Tree (SingletonIndex.mk b) = encode Tree b := by simp

example {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ a, UniqueEncoding Tree (β a)] (a : α) (b : β a) :
    encode Tree (Sigma.mk a b) = encode Tree (a, b) := by simp

example : decode (Language.booleanAlgebra.Functions 1) (encode Tree BooleanAlgebra.infFunc) =
    Part.none := rfl

example (t : Complexity.Tree) : decode (Language.booleanAlgebra.Functions 3) t = Part.none := by
  apply Part.eq_none_iff.mpr
  intro op
  cases op

def rebuildGate (x : Value) : Code Value :=
  BooleanAlgebra.Code.matchOn x
    BooleanAlgebra.Code.inf BooleanAlgebra.Code.sup BooleanAlgebra.Code.compl
    BooleanAlgebra.Code.bot BooleanAlgebra.Code.top

example {k : ℕ} (op : Language.booleanAlgebra.Functions k) :
    (rebuildGate .input).Computes (encode Tree op) (encode Tree op) := by
  cases op <;> simp [computes_iff, rebuildGate]

example : encode Tree BooleanAlgebra.infFunc = encode Tree ((), ()) := by simp

-- The command exposes the supplied family, without a second instance for its implementation.
example : True := by
  fail_if_success have := (inferInstance : UniqueEncoding Tree (booleanAlgebraFunc 2))
  trivial

structure Payload (α : Type*) where
  value : α

structure Signature where
  Data : Type u

def signature (α : Type u) : Signature.{u} := ⟨Payload α⟩

namespace Projected

tree_encoding (fun α => (signature α).Data)

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    encode Tree (α := (signature α).Data) ⟨a⟩ = encode Tree a := by simp

example {α : Type*} [UniqueEncoding Tree α] (p : (signature α).Data) :
    (Code.mk .input).Computes (encode Tree p.value) (encode Tree p) := by
  cases p
  simp [computes_iff]

end Projected

-- A section variable and a specialized universe must survive generalization.
def fixedSignature (α : Type) : Signature := ⟨Payload α⟩

namespace FixedUniverse

variable (α : Type) in
tree_encoding (fixedSignature α).Data

example {α : Type} [UniqueEncoding Tree α] :
    UniqueEncoding Tree (fixedSignature α).Data := inferInstance

end FixedUniverse

def recursiveSignature (α : Type) : Signature := ⟨List α⟩

/-- error: Tree encoding through a type expression currently supports non-recursive inductive types; recursive aliases also need compatible elimination principles -/
#guard_msgs in
tree_encoding (fun α => (recursiveSignature α).Data)

/-- error: Tree encoding expects all inductive parameters and indices to be variables; supply the complete type family -/
#guard_msgs in
tree_encoding Language.booleanAlgebra.Functions 2

run_cmd do
  for name in [``Fixed.treeEncoding, ``Mixed.treeEncoding, ``SingletonIndex.treeEncoding,
      ``Recursive.treeEncoding, ``Sigma.treeEncoding, ``BooleanAlgebra.treeEncoding,
      ``Projected.treeEncoding, ``FixedUniverse.treeEncoding] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on an unfinished proof"

end IndexedEncodingTest
