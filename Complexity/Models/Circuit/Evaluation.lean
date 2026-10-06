/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic

/-!
# Evaluation with an array of wire values

`evalVector` stores each gate result in an array-backed `Vector`. Repeated wire references read
the stored value, and each stored gate is evaluated once in topological order.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

variable {L : Language} {M : Type*} [L.Structure M] {n m : ℕ}

/-- Evaluate once per stored gate, storing the available wire values in a vector. -/
def evalVector : {n m : ℕ} → Circuit L n m → Vector M n → Vector M m
  | _, _, .outputs select, x => Vector.ofFn fun i => x[(select i).val]
  | _, _, .gate op args next, x =>
      next.evalVector (x.push (Structure.funMap op fun i => x[(args i).val]))

private theorem vector_ofFn_snoc (x : Fin n → M) (y : M) :
    Vector.ofFn (Fin.snoc x y) = (Vector.ofFn x).push y := by
  rw [Vector.ofFn_succ]
  simp only [Fin.snoc_castSucc]
  change (Vector.ofFn x).push (Fin.snoc (α := fun _ => M) x y (Fin.last n)) = _
  rw [Fin.snoc_last]

/-- The vector evaluator agrees with the functional semantics. -/
@[simp] theorem evalVector_ofFn (c : Circuit L n m) (x : Fin n → M) :
    c.evalVector (Vector.ofFn x) = Vector.ofFn (c.eval x) := by
  induction c with
  | outputs _ => simp [evalVector, Function.comp_def]
  | gate op args next ih =>
      simp only [evalVector, Vector.getElem_ofFn, ← vector_ofFn_snoc, ih, eval_gate,
        Function.comp_def]

/-- Read a designated output from the vector evaluator. -/
@[simp] theorem getElem_evalVector (c : Circuit L n m) (x : Vector M n) (i : Fin m) :
    (c.evalVector x)[i.val] = c.eval (fun j => x[j.val]) i := by
  have h := congrArg (fun y : Vector M m => y[i.val])
    (c.evalVector_ofFn (fun j => x[j.val]))
  simpa using h

end Complexity.Circuit
