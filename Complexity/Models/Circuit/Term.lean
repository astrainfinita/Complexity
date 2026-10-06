/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Composition

/-!
# Circuits and first-order terms

Every designated output has a term with the same interpretation. Unfolding may duplicate shared
subexpressions, so the size of these terms is not a circuit-size measure. Conversely, `ofTerm`
compiles an expression tree to a single-output circuit; it does not identify equal subterms.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

variable {L : Language} {M : Type*} {n m : ℕ}

/-- Unfold each output as a term in the input variables. This can expand sharing exponentially. -/
def toTerms (c : Circuit L n m) : Fin m → L.Term (Fin n) :=
  c.evalWith (fun f args => Term.func f args) Term.var

/-- Unfolding a circuit into terms preserves its output values. -/
@[simp] theorem realize_toTerms [L.Structure M] (c : Circuit L n m)
    (x : Fin n → M) (j : Fin m) : (c.toTerms j).realize x = c.eval x j := by
  have h := c.map_evalWith (fun f args => Term.func f args) Structure.funMap
    (Term.realize x) (fun _ _ => rfl) Term.var
  exact congrFun h j

/-- Compile a first-order term into a circuit, with one gate per function-symbol occurrence. -/
def ofTerm : L.Term (Fin n) → Circuit L n 1
  | .var i => outputs fun _ => i
  | .func op args => (bundle fun i => ofTerm (args i)).comp (ofGate op _root_.id)

/-- The circuit compiled from a term has its usual first-order interpretation. -/
@[simp] theorem eval_ofTerm [L.Structure M] (t : L.Term (Fin n)) (x : Fin n → M) :
    (ofTerm t).eval x 0 = t.realize x := by
  induction t with
  | var _ => rfl
  | func op args ih => simp [ofTerm, ih, Term.realize]

@[simp] theorem size_ofTerm_var (i : Fin n) :
    (ofTerm (Term.var i : L.Term (Fin n))).size = 0 := rfl

/-- Term compilation counts each occurrence, including repeated equal subterms. -/
@[simp] theorem size_ofTerm_func {k : ℕ} (op : L.Functions k)
    (args : Fin k → L.Term (Fin n)) :
    (ofTerm (.func op args)).size = (∑ i, (ofTerm (args i)).size) + 1 := by simp [ofTerm]

end Complexity.Circuit
