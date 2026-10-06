/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Composition

/-!
# Replacing gates by circuits

Each source gate is implemented by a single-output target circuit. Compilation inserts that
implementation once, retaining its output wire for all later uses.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {M : Type w} {n m : ℕ}

/-- Replace each gate by an implementation circuit, preserving shared intermediate results. -/
def compile (impl : ∀ {k}, L.Functions k → Circuit L' k 1) :
    {n m : ℕ} → Circuit L n m → Circuit L' n m
  | _, _, .outputs select => .outputs select
  | _, _, .gate op args next =>
      ((impl op).relabel args).keepInputs.comp (next.compile impl)

/-- Compilation uses exactly the sum of the sizes of the chosen gate implementations. -/
@[simp] theorem size_compile (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1) :
    (c.compile impl).size = c.cost (fun op => (impl op).size) := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [compile, cost, ih]

/-- A uniform bound on implementation sizes gives a linear bound on the compiled gate count. -/
theorem size_compile_le (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1) (b : ℕ)
    (h : ∀ {k} (op : L.Functions k), (impl op).size ≤ b) :
    (c.compile impl).size ≤ b * c.size := by
  rw [size_compile]
  induction c with
  | outputs _ => simp [cost]
  | gate op args next ih =>
      simpa [cost, Nat.mul_add, Nat.add_comm] using Nat.add_le_add (h op) ih

/-- Correct implementations of individual gates give a correct compiled circuit. -/
theorem evalWith_compile (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1)
    (ops : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (ops' : ∀ {k}, L'.Functions k → (Fin k → M) → M)
    (h : ∀ {k} (op : L.Functions k) x, (impl op).evalWith ops' x 0 = ops op x)
    (x : Fin n → M) : (c.compile impl).evalWith ops' x = c.evalWith ops x := by
  induction c with
  | outputs _ => rfl
  | gate op args next ih =>
      simp only [compile, evalWith_comp, evalWith_keepInputs, evalWith_relabel, ih, evalWith_gate]
      rw [Fin.append_right_eq_snoc, h]

/-- Specialize gate replacement correctness to first-order structure interpretations. -/
theorem eval_compile [L.Structure M] [L'.Structure M] (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1)
    (h : ∀ {k} (op : L.Functions k) (x : Fin k → M),
      (impl op).eval x 0 = Structure.funMap op x)
    (x : Fin n → M) : (c.compile impl).eval x = c.eval x :=
  c.evalWith_compile impl _ _ h x

end Complexity.Circuit
