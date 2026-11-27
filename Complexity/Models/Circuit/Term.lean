/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Composition
public import Complexity.ModelTheory.Term
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Circuits and first-order terms

Every designated output has a term with the same interpretation. Unfolding may duplicate shared
subexpressions, so the size of these terms is not a circuit-size measure. Conversely, `ofTerm`
compiles an expression tree to a single-output circuit with one gate per function-symbol occurrence
(`size_ofTerm`), `ofTerms` compiles one term per output without sharing equal subterms, and
`ofTermsEquiv` compiles terms indexed by arbitrary finite types through equivalences with `Fin`
(with gate-count sum `size_ofTermsEquiv` and uniform bound `size_ofTermsEquiv_le`).
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

theorem size_ofTerm_var (i : Fin n) :
    (ofTerm (Term.var i : L.Term (Fin n))).size = 0 := rfl

theorem size_ofTerm_func {k : ℕ} (op : L.Functions k)
    (args : Fin k → L.Term (Fin n)) :
    (ofTerm (.func op args)).size = (∑ i, (ofTerm (args i)).size) + 1 := by simp [ofTerm]

/-- Term compilation counts each occurrence, including repeated equal subterms. -/
@[simp] theorem size_ofTerm (t : L.Term (Fin n)) : (ofTerm t).size = t.numFuncs := by
  induction t with
  | var i => rfl
  | func op args ih => simp [size_ofTerm_func, ih]

/-- Compile one term for each output. Equal subterms, also across outputs, are not shared. -/
def ofTerms (t : Fin m → L.Term (Fin n)) : Circuit L n m :=
  bundle fun j => ofTerm (t j)

@[simp] theorem eval_ofTerms [L.Structure M] (t : Fin m → L.Term (Fin n)) (x : Fin n → M) :
    (ofTerms t).eval x = fun j => (t j).realize x := by
  simp [ofTerms]

@[simp] theorem size_ofTerms (t : Fin m → L.Term (Fin n)) :
    (ofTerms t).size = ∑ j, (t j).numFuncs := by
  simp [ofTerms]

variable {α β : Type*}

/-- Compile one term for each output, with the variables numbered by `eIn` and the outputs by
`eOut`. -/
def ofTermsEquiv (eIn : α ≃ Fin n) (eOut : β ≃ Fin m) (t : β → L.Term α) : Circuit L n m :=
  ofTerms fun j => (t (eOut.symm j)).relabel eIn

@[simp] theorem eval_ofTermsEquiv [L.Structure M] (eIn : α ≃ Fin n) (eOut : β ≃ Fin m)
    (t : β → L.Term α) (x : Fin n → M) :
    (ofTermsEquiv eIn eOut t).eval x = (fun b => (t b).realize (x ∘ eIn)) ∘ eOut.symm := by
  simp [ofTermsEquiv, Function.comp_def]

@[simp] theorem size_ofTermsEquiv [Fintype β] (eIn : α ≃ Fin n) (eOut : β ≃ Fin m)
    (t : β → L.Term α) : (ofTermsEquiv eIn eOut t).size = ∑ b, (t b).numFuncs := by
  simp only [ofTermsEquiv, size_ofTerms, Term.numFuncs_relabel]
  exact Equiv.sum_comp eOut.symm (fun b => (t b).numFuncs)

/-- A bound on every output term bounds the gate count by the number of outputs times it. -/
theorem size_ofTermsEquiv_le {k : ℕ} (eIn : α ≃ Fin n) (eOut : β ≃ Fin m) {t : β → L.Term α}
    (h : ∀ b, (t b).numFuncs ≤ k) : (ofTermsEquiv eIn eOut t).size ≤ m * k := by
  simp only [ofTermsEquiv, size_ofTerms, Term.numFuncs_relabel]
  exact (Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ h (eOut.symm j)).trans_eq <| by
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Complexity.Circuit
