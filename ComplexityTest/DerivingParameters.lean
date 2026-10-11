/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Language.Derive

namespace DerivingParametersTest

open Complexity

def enabled : Bool := true

@[tree_encoding]
inductive Packet : Bool → Type where
  | mk (value : Bool) : Packet enabled

def dimensions : ℕ × Bool := (2, true)

@[tree_encoding]
inductive SizedPacket : (ℕ × Bool) → Type where
  | mk (value : Bool) : SizedPacket dimensions

example (value : Bool) : encode Tree (Packet.mk value) = encode Tree value := by simp

example : decode (Packet false) Complexity.Tree.nil = Part.none := rfl

example : decode (SizedPacket (1, true)) Complexity.Tree.nil = Part.none := rfl

example : decode (SizedPacket (2, false)) Complexity.Tree.nil = Part.none := rfl

example (b : Bool) (p : Packet b) (t : Tree) :
    p ∈ decode (Packet b) t ↔ encode Tree p = t := UniqueEncoding.mem_decode_iff

example (p : Packet enabled) : decode (Packet enabled) (encode Tree p) = Part.some p :=
  UniqueEncoding.decode_encode p

structure Payload (α : Type u) where
  value : α

structure Signature where
  Data : Type u

def signature (_mode : Bool) (α : Type u) : Signature.{u} := ⟨Payload α⟩

namespace Captured

variable (mode : Bool) in
 tree_encoding (fun α => (signature mode α).Data)

example (mode : Bool) {α : Type u} [UniqueEncoding Tree α] (a : α) :
    encode Tree (α := (signature mode α).Data) ⟨a⟩ = encode Tree a := by simp

example (mode : Bool) {α : Type u} [UniqueEncoding Tree α]
    (p : (signature mode α).Data) (t : Tree) :
    p ∈ decode ((signature mode α).Data) t ↔ encode Tree p = t :=
  UniqueEncoding.mem_decode_iff

example (mode : Bool) :
    decode ((signature mode Bool).Data) (Complexity.Tree.pair .nil (.pair .nil .nil)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro p hp
  have h := UniqueEncoding.mem_decode_iff.mp hp
  cases p with
  | mk b => cases b <;> simp at h

end Captured

-- The type parameter must precede the captured value that depends on it.
def dependentSignature (α : Type u) (_witness : α) : Signature.{u} := ⟨Payload α⟩

namespace DependentCaptured

variable (α : Type u) (witness : α) in
 tree_encoding (dependentSignature α witness).Data

example {α : Type u} [UniqueEncoding Tree α] (witness a : α) :
    encode Tree (α := (dependentSignature α witness).Data) ⟨a⟩ = encode Tree a := by simp

example {α : Type u} [UniqueEncoding Tree α] (witness : α)
    (p : (dependentSignature α witness).Data) :
    decode ((dependentSignature α witness).Data) (encode Tree p) = Part.some p :=
  UniqueEncoding.decode_encode p

end DependentCaptured

class Marker (α : Type u) where
  value : Bool

def markedSignature (α : Type u) [Marker α] : Signature.{u} := ⟨Payload α⟩

namespace CapturedInstance

variable (α : Type u) [Marker α] in
 tree_encoding (markedSignature α).Data

example {α : Type u} [Marker α] [UniqueEncoding Tree α] (a : α) :
    encode Tree (α := (markedSignature α).Data) ⟨a⟩ = encode Tree a := by simp

end CapturedInstance

-- A captured dependency on an index is safe if no constructor fixes that index.
inductive Flexible : Bool → Type where
  | mk (b : Bool) (value : Bool) : Flexible b

def flexibleSignature (b : Bool) (_h : b = true) : Signature := ⟨Flexible b⟩

namespace CapturedIndex

variable (b : Bool) (h : b = true) in
 tree_encoding (flexibleSignature b h).Data

example (b : Bool) (h : b = true) : UniqueEncoding Tree (flexibleSignature b h).Data :=
  inferInstance

end CapturedIndex

opaque hidden : Bool := true

/-- error: Tree encoding requires closed constructor indices to reduce to patterns; cannot match hidden -/
#guard_msgs in
@[tree_encoding]
inductive HiddenIndex : Bool → Type where
  | mk : HiddenIndex hidden

inductive Indexed : Bool → Type where
  | mk : Indexed true

def dependentIndexSignature (b : Bool) (_h : b = true) : Signature := ⟨Indexed b⟩

/-- error: Tree encoding cannot specialize captured parameters depending on fixed indices -/
#guard_msgs in
variable (b : Bool) (h : b = true) in
 tree_encoding (dependentIndexSignature b h).Data

run_cmd do
  for name in [``Packet.treeEncoding, ``SizedPacket.treeEncoding,
      ``Captured.treeEncoding, ``DependentCaptured.treeEncoding,
      ``CapturedInstance.treeEncoding, ``CapturedIndex.treeEncoding] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on an unfinished proof"
  for name in [``Captured.treeEncoding, ``Captured.treeEncode, ``Captured.treeDecode,
      ``Captured.treeDecode_iff, ``DependentCaptured.treeEncoding,
      ``CapturedInstance.treeEncoding] do
    if (← Lean.getConstInfo name).type.containsConst (· == ``Payload) then
      throwError "{name} exposes the implementation type"

example : True := by
  fail_if_success have := (inferInstance : UniqueEncoding Tree (Payload Bool))
  fail_if_success have := HiddenIndex.treeEncode
  trivial

end DerivingParametersTest
