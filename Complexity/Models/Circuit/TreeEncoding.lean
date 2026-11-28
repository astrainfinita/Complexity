/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic
public import Complexity.Models.TreeMachine.Language.CaseView
public import Complexity.Encoding.Nat
public import Complexity.Encoding.Fin
public import Complexity.Encoding.FinVector
public import Complexity.Encoding.Sigma

/-! # Tree encodings and matchers for circuits

A circuit is encoded directly as a tree whose wire tables are `FinVector`s, so its encoding does not
depend on `UniqueEncoding Tree (Fin n → α)`. Input and output counts are supplied by the circuit
type. A gate stores its arity, operation symbol, input wires, and continuation, in that order.

Programs see the wire tables of a circuit only as `FinVector`s. A `match` on a circuit binds them as
functions `Fin k → Fin n`, so it is not translated: `Circuit.caseView` is not an instance. Programs
match with `Circuit.casesFinVector`, or with `casesFinVectorOutputs` and `casesFinVectorGate` when
one constructor is excluded, whose branches receive the wire tables as `FinVector`s; their
translation rules use `Circuit.caseView`.
-/

@[expose] public section

namespace Complexity

open FirstOrder FirstOrder.Language

universe u v

namespace Circuit

variable {L : Language.{u, v}} {n m : ℕ}

/-- Case analysis on a circuit whose branches receive the wire tables as `FinVector`s, together
with the equation of the circuit. -/
def casesFinVector {β : Sort*} (c : Circuit L n m)
    (outputs : (v : FinVector (Fin n) m) → c = .outputs v.get → β)
    (gate : {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin n) k) →
      (next : Circuit L (n + 1) m) → c = .gate op v.get next → β) : β :=
  match (generalizing := false) h : c with
  | .outputs select => outputs (.ofFn select) h
  | .gate op args next => gate op (.ofFn args) next h

attribute [dominated_simp] casesFinVector.eq_def

section casesFinVector

variable {β : Sort*}

@[simp] theorem casesFinVector_outputs (select : Fin m → Fin n)
    (outputs : (v : FinVector (Fin n) m) → Circuit.outputs select = .outputs v.get → β)
    (gate : {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin n) k) →
      (next : Circuit L (n + 1) m) → Circuit.outputs select = .gate op v.get next → β) :
    (Circuit.outputs select).casesFinVector outputs gate = outputs (.ofFn select) rfl :=
  rfl

@[simp] theorem casesFinVector_gate {k : ℕ} (op : L.Functions k) (args : Fin k → Fin n)
    (next : Circuit L (n + 1) m)
    (outputs : (v : FinVector (Fin n) m) → Circuit.gate op args next = .outputs v.get → β)
    (gate : {k : ℕ} → (op' : L.Functions k) → (v : FinVector (Fin n) k) →
      (next' : Circuit L (n + 1) m) → Circuit.gate op args next = .gate op' v.get next' → β) :
    (Circuit.gate op args next).casesFinVector outputs gate = gate op (.ofFn args) next rfl :=
  rfl

variable {c : Circuit L n m} (outputs : (v : FinVector (Fin n) m) → c = .outputs v.get → β)
  (gate : {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin n) k) →
    (next : Circuit L (n + 1) m) → c = .gate op v.get next → β)

theorem casesFinVector_of_eq_outputs {v : FinVector (Fin n) m} (h : c = .outputs v.get) :
    c.casesFinVector outputs gate = outputs v h := by
  subst h
  rfl

theorem casesFinVector_of_eq_gate {k : ℕ} {op : L.Functions k} {v : FinVector (Fin n) k}
    {next : Circuit L (n + 1) m} (h : c = .gate op v.get next) :
    c.casesFinVector outputs gate = gate op v next h := by
  subst h
  rfl

end casesFinVector

/-- `casesFinVector` on a circuit that is not a gate. -/
def casesFinVectorOutputs {β : Sort*} (c : Circuit L n m)
    (outputs : (v : FinVector (Fin n) m) → c = .outputs v.get → β)
    (notGate : ∀ {k : ℕ} (op : L.Functions k) (v : FinVector (Fin n) k)
      (next : Circuit L (n + 1) m), c = .gate op v.get next → False) : β :=
  c.casesFinVector outputs fun op v next h => (notGate op v next h).elim

/-- `casesFinVector` on a circuit that is a gate. -/
def casesFinVectorGate {β : Sort*} (c : Circuit L n m)
    (notOutputs : ∀ v : FinVector (Fin n) m, c = .outputs v.get → False)
    (gate : {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin n) k) →
      (next : Circuit L (n + 1) m) → c = .gate op v.get next → β) : β :=
  c.casesFinVector (fun v h => (notOutputs v h).elim) gate

variable [∀ k, UniqueEncoding Tree (L.Functions k)]

/-- Encode a circuit as a tree, storing wire tables as `FinVector`s. -/
def treeEncode : {n m : ℕ} → Circuit L n m → Tree
  | _, _, .outputs select => .pair .nil ⌜FinVector.ofFn select⌝ₜ
  | _, _, .gate (k := k) op args next =>
      .pair (.pair .nil .nil)
        (.pair ⌜k⌝ₜ (.pair ⌜op⌝ₜ (.pair ⌜FinVector.ofFn args⌝ₜ (treeEncode next))))

/-- Decode a circuit from its tree code. -/
def treeDecode : {n m : ℕ} → Tree → Part (Circuit L n m)
  | n, m, .pair .nil s =>
      (decode (FinVector (Fin n) m) s).map fun select => .outputs select.get
  | n, _, .pair (.pair .nil .nil) (.pair tk (.pair top (.pair targs tnext))) =>
      (decode ℕ tk).bind fun k =>
        (decode (L.Functions k) top).bind fun op =>
          (decode (FinVector (Fin n) k) targs).bind fun args =>
            (treeDecode tnext).map fun next => .gate op args.get next
  | _, _, _ => Part.none

theorem treeDecode_iff (c : Circuit L n m) (t : Tree) :
    c ∈ treeDecode t ↔ treeEncode c = t := by
  induction c generalizing t with
  | outputs select =>
    unfold treeDecode treeEncode
    split
    · simp only [Part.mem_map_iff, UniqueEncoding.mem_decode_iff, Tree.pair, Tree.nil,
        BinaryTree.node.injEq, true_and]
      exact ⟨fun ⟨v, hv, h⟩ => by cases h; exact hv,
        fun h => ⟨FinVector.ofFn select, h, rfl⟩⟩
    · simp [Tree.pair, Tree.nil]
    · simp_all [Tree.pair, Tree.nil, eq_comm]
  | gate op args next ih =>
    unfold treeDecode treeEncode
    split
    · simp [Tree.pair, Tree.nil]
    · simp only [Part.mem_bind_iff, Part.mem_map_iff, UniqueEncoding.mem_decode_iff,
        Tree.pair, Tree.nil, BinaryTree.node.injEq, true_and]
      constructor
      · rintro ⟨k', hk, op', hop, args', hargs, next', hnext, heq⟩
        cases heq
        exact ⟨hk, hop, hargs, (ih _).mp hnext⟩
      · rintro ⟨hk, hop, hargs, hnext⟩
        exact ⟨_, hk, op, hop, FinVector.ofFn args, hargs, next, (ih _).mpr hnext, rfl⟩
    · simp_all [Tree.pair, Tree.nil, eq_comm]

/-- A circuit uses the tree code with `FinVector` wire tables directly, without an auxiliary
layout. -/
instance treeEncoding : UniqueEncoding Tree (Circuit L n m) where
  decode := treeDecode
  encode := treeEncode
  mem_decode_iff := treeDecode_iff _ _

@[simp, dominated_simp] theorem encode_outputs (select : Fin m → Fin n) :
    ⌜(outputs select : Circuit L n m)⌝ₜ = ⌜((), FinVector.ofFn select)⌝ₜ := rfl

@[simp, dominated_simp] theorem encode_gate {k : ℕ} (op : L.Functions k)
    (args : Fin k → Fin n) (next : Circuit L (n + 1) m) :
    ⌜gate op args next⌝ₜ = ⌜(((), ()), k, op, FinVector.ofFn args, next)⌝ₜ := rfl

theorem size_le_size_encode (c : Circuit L n m) : c.size ≤ ⌜c⌝ₜ.size := by
  induction c with
  | outputs _ => exact Nat.zero_le _
  | gate op args next ih =>
    simp only [size_gate, encode_gate, size_encode_prod, size_encode_unit]
    omega

theorem outputs_le_size_encode (c : Circuit L n m) : m ≤ ⌜c⌝ₜ.size := by
  induction c with
  | outputs select =>
    have := card_le_size_encode_finVector (FinVector.ofFn select)
    simp only [encode_outputs, size_encode_prod, size_encode_unit]
    omega
  | gate op args next ih =>
    simp only [encode_gate, size_encode_prod, size_encode_unit]
    omega

open TreeProgram in
/-- The constructors of `Circuit L n m` with their wire tables as `FinVector`s, as in the tree
encoding. It is not an instance, so that a `match` on a circuit, which binds the wire tables as
functions, is not translated; the translation rules of `casesFinVector` and its variants use it.
Its `elim` is `casesFinVector`. -/
@[instance_reducible] def caseView : CaseView (Circuit L n m) 2 where
  Payload i := match i with
    | 0 => ULift (FinVector (Fin n) m)
    | 1 => Σ k, L.Functions k × FinVector (Fin n) k × Circuit L (n + 1) m
  encoding i := match i with
    | 0 => inferInstanceAs (UniqueEncoding Tree (ULift (FinVector (Fin n) m)))
    | 1 => inferInstanceAs
        (UniqueEncoding Tree (Σ k, L.Functions k × FinVector (Fin n) k × Circuit L (n + 1) m))
  ofPayload i p := match i with
    | 0 => .outputs p.down.get
    | 1 => .gate p.2.1 p.2.2.1.get p.2.2.2
  exists_ofPayload c := match c with
    | .outputs select => ⟨0, ⟨FinVector.ofFn select⟩, rfl⟩
    | .gate op args next => ⟨1, ⟨_, op, FinVector.ofFn args, next⟩, rfl⟩
  elim c g := c.casesFinVector (fun v h => g 0 ⟨v⟩ h) fun op v next h => g 1 ⟨_, op, v, next⟩ h
  elim_ofPayload i p _ := match i, p with
    | 0, ⟨_⟩ => rfl
    | 1, ⟨_, _, _, _⟩ => rfl
  dispatch := .test [false] (.leaf 1 [true]) (.leaf 0 [true])
  select_encode i p := match i, p with
    | 0, ⟨_⟩ => rfl
    | 1, ⟨_, _, _, _⟩ => rfl

end Circuit

end Complexity
