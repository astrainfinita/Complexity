/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.ModelTheory.Syntax
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting function symbols in first-order terms

`Term.numFuncs` counts the occurrences of function symbols in a term, counting repeated subterms
separately.
-/

@[expose] public section

namespace FirstOrder.Language.Term

variable {L : Language} {α β : Type*}

/-- The number of occurrences of function symbols, counting repeated subterms separately. -/
def numFuncs : L.Term α → ℕ
  | var _ => 0
  | func _ ts => (∑ i, (ts i).numFuncs) + 1

@[simp] theorem numFuncs_var (a : α) : (var a : L.Term α).numFuncs = 0 := rfl

@[simp] theorem numFuncs_func {l : ℕ} (f : L.Functions l) (ts : Fin l → L.Term α) :
    (func f ts).numFuncs = (∑ i, (ts i).numFuncs) + 1 := rfl

@[simp] theorem numFuncs_relabel (g : α → β) (t : L.Term α) :
    (t.relabel g).numFuncs = t.numFuncs := by
  induction t with
  | var => rfl
  | func f ts ih => simp [relabel, ih]

@[simp] theorem numFuncs_functions_apply₁ (f : L.Functions 1) (t : L.Term α) :
    (f.apply₁ t).numFuncs = t.numFuncs + 1 := by
  simp [Functions.apply₁]

@[simp] theorem numFuncs_functions_apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) :
    (f.apply₂ t₁ t₂).numFuncs = t₁.numFuncs + t₂.numFuncs + 1 := by
  simp [Functions.apply₂, Fin.sum_univ_two]

@[simp] theorem numFuncs_constants (c : L.Constants) :
    (c.term : L.Term α).numFuncs = 1 := by
  simp [Constants.term]

end FirstOrder.Language.Term
