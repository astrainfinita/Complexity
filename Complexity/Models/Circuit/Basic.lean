/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Circuits over a first-order language

`Circuit L n m` is a straight-line circuit with `n` inputs and `m` outputs. Each gate uses
a function symbol of `L` and appends one wire to the environment available to its continuation.
Wire indices therefore rule out forward references and cycles. Reusing an index retains sharing.
Relations in `L` play no role in a circuit.

Inputs, wiring, and output selection cost no gates. Every stored gate, including a constant or
an unused gate, contributes one to `size`. Zero inputs and zero outputs are supported.

`evalWith` evaluates using an explicit interpretation; `eval` uses `L.Structure`.
-/

@[expose] public section

universe u v w w'

namespace Complexity

open FirstOrder FirstOrder.Language

/-- An acyclic circuit. A gate adds its result at index `n`, keeping all previous indices. -/
inductive Circuit (L : Language.{u, v}) : ℕ → ℕ → Type u where
  /-- Select, permute, or duplicate available wires as outputs. -/
  | outputs {n m : ℕ} (select : Fin m → Fin n) : Circuit L n m
  /-- Compute one gate and continue with its result appended to the available wires. -/
  | gate {n m k : ℕ} (op : L.Functions k) (args : Fin k → Fin n)
      (next : Circuit L (n + 1) m) : Circuit L n m

namespace Circuit

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {n m k : ℕ}

/-- The number of stored operation gates, including constants and unused gates. -/
def size : {n m : ℕ} → Circuit L n m → ℕ
  | _, _, .outputs _ => 0
  | _, _, .gate _ _ next => next.size + 1

@[simp] theorem size_outputs (select : Fin m → Fin n) :
    (outputs select : Circuit L n m).size = 0 := rfl

@[simp] theorem size_gate (op : L.Functions k) (args : Fin k → Fin n)
    (next : Circuit L (n + 1) m) : (gate op args next).size = next.size + 1 := rfl

/-- Evaluate with an explicit interpretation of the function symbols. -/
def evalWith (f : ∀ {k}, L.Functions k → (Fin k → M) → M) :
    {n m : ℕ} → Circuit L n m → (Fin n → M) → (Fin m → M)
  | _, _, .outputs select, x => x ∘ select
  | _, _, .gate op args next, x =>
      let value := f op (x ∘ args)
      next.evalWith f (Fin.snoc x value)

@[simp] theorem evalWith_outputs (f : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (select : Fin m → Fin n) (x : Fin n → M) :
    (outputs select : Circuit L n m).evalWith f x = x ∘ select := rfl

@[simp] theorem evalWith_gate (f : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (op : L.Functions k) (args : Fin k → Fin n) (next : Circuit L (n + 1) m)
    (x : Fin n → M) :
    (gate op args next).evalWith f x = next.evalWith f (Fin.snoc x (f op (x ∘ args))) := rfl

/-- Evaluate a circuit using the interpretation provided by `L.Structure M`. -/
def eval [L.Structure M] (c : Circuit L n m) (x : Fin n → M) : Fin m → M :=
  c.evalWith Structure.funMap x

@[simp] theorem eval_outputs [L.Structure M] (select : Fin m → Fin n) (x : Fin n → M) :
    (outputs select : Circuit L n m).eval x = x ∘ select := rfl

@[simp] theorem eval_gate [L.Structure M] (op : L.Functions k) (args : Fin k → Fin n)
    (next : Circuit L (n + 1) m) (x : Fin n → M) :
    (gate op args next).eval x =
      next.eval (Fin.snoc x (Structure.funMap op (x ∘ args))) := rfl

/-- A circuit computes a function when their outputs agree on every input. -/
def Computes [L.Structure M] (c : Circuit L n m)
    (f : (Fin n → M) → Fin m → M) : Prop := ∀ x, c.eval x = f x

/-- The zero-gate identity circuit. -/
def id (L : Language) (n : ℕ) : Circuit L n n := outputs _root_.id

@[simp] theorem size_id : (id L n).size = 0 := rfl

@[simp] theorem evalWith_id (f : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (x : Fin n → M) : (id L n).evalWith f x = x := rfl

@[simp] theorem eval_id [L.Structure M] (x : Fin n → M) : (id L n).eval x = x := rfl

/-- Apply a single operation to selected input wires. -/
def ofGate (op : L.Functions k) (args : Fin k → Fin n) : Circuit L n 1 :=
  gate op args (outputs fun _ => Fin.last n)

@[simp] theorem size_ofGate (op : L.Functions k) (args : Fin k → Fin n) :
    (ofGate op args).size = 1 := rfl

@[simp] theorem evalWith_ofGate (f : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (op : L.Functions k) (args : Fin k → Fin n) (x : Fin n → M) :
    (ofGate op args).evalWith f x = fun _ => f op (x ∘ args) := by
  funext i
  simp [ofGate, Function.comp_def]

@[simp] theorem eval_ofGate [L.Structure M] (op : L.Functions k)
    (args : Fin k → Fin n) (x : Fin n → M) :
    (ofGate op args).eval x = fun _ => Structure.funMap op (x ∘ args) :=
  evalWith_ofGate _ _ _ _

/-- An operation-preserving map commutes with the evaluation of a circuit. -/
theorem map_evalWith (c : Circuit L n m)
    (f : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (g : ∀ {k}, L.Functions k → (Fin k → N) → N) (h : M → N)
    (hh : ∀ {k} (op : L.Functions k) x, h (f op x) = g op (h ∘ x))
    (x : Fin n → M) : h ∘ c.evalWith f x = c.evalWith g (h ∘ x) := by
  induction c with
  | outputs select => rfl
  | gate op args next ih =>
      simpa only [evalWith_gate, Fin.comp_snoc, hh, Function.comp_assoc] using
        ih (Fin.snoc x (f op (x ∘ args)))

/-- Evaluation commutes with mathlib's homomorphisms of first-order structures. -/
theorem map_eval [L.Structure M] [L.Structure N] {F : Type*}
    [FunLike F M N] [HomClass L F M N] (c : Circuit L n m) (h : F) (x : Fin n → M) :
    h ∘ c.eval x = c.eval (h ∘ x) :=
  c.map_evalWith _ _ h (fun op y => HomClass.map_fun h op y) x

/-- Require a property of every gate symbol. Gate permissions are independent of semantics. -/
def Uses (P : ∀ {k}, L.Functions k → Prop) : {n m : ℕ} → Circuit L n m → Prop
  | _, _, .outputs _ => True
  | _, _, .gate op _ next => P op ∧ next.Uses P

instance instDecidableUses (P : ∀ {k}, L.Functions k → Prop)
    [∀ k, DecidablePred (@P k)] : {n m : ℕ} → (c : Circuit L n m) → Decidable (c.Uses P)
  | _, _, .outputs _ => isTrue trivial
  | _, _, .gate op _ next =>
      @instDecidableAnd _ _ (inferInstance : Decidable (P op)) (instDecidableUses P next)

/-- Every gate has at most `r` inputs; there need not be a bound on the language itself. -/
def FanInAtMost (c : Circuit L n m) (r : ℕ) : Prop := c.Uses fun {k} _ => k ≤ r

instance (c : Circuit L n m) (r : ℕ) : Decidable (c.FanInAtMost r) :=
  inferInstanceAs (Decidable (c.Uses fun {k} _ => k ≤ r))

/-- Sum a chosen natural-number cost over stored gates. -/
def cost (weight : ∀ {k}, L.Functions k → ℕ) : {n m : ℕ} → Circuit L n m → ℕ
  | _, _, .outputs _ => 0
  | _, _, .gate op _ next => weight op + next.cost weight

@[simp] theorem cost_one (c : Circuit L n m) : c.cost (fun _ => 1) = c.size := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [cost, ih, Nat.add_comm]

end Circuit

end Complexity
