/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.List.Basic

/-! # Literals and conjunctive normal forms

A literal records a variable and the Boolean value satisfying it. Clauses and CNFs are lists,
retaining order and repeated occurrences. Evaluation uses disjunction within each clause and
conjunction between clauses.
-/

@[expose] public section

namespace Complexity

namespace CNF

/-- A signed variable; `true` is positive polarity and `false` is negative polarity. -/
@[ext]
structure Literal (α : Type*) where
  /-- The underlying variable. -/
  atom : α
  /-- The value of the variable that satisfies this literal. -/
  polarity : Bool
  deriving DecidableEq

namespace Literal

variable {α β γ : Type*}

/-- A positive literal. -/
abbrev pos (a : α) : Literal α := ⟨a, true⟩

/-- A negative literal. -/
abbrev neg (a : α) : Literal α := ⟨a, false⟩

/-- Rename the variable, retaining its polarity. -/
@[simps]
def map (f : α → β) (l : Literal α) : Literal β := ⟨f l.atom, l.polarity⟩

@[simp] theorem map_id (l : Literal α) : l.map id = l := rfl

@[simp] theorem map_map (f : α → β) (g : β → γ) (l : Literal α) :
    (l.map f).map g = l.map (g ∘ f) := rfl

/-- Reverse the polarity of a literal. -/
@[simps]
def negate (l : Literal α) : Literal α := { l with polarity := !l.polarity }

@[simp] theorem negate_negate (l : Literal α) : l.negate.negate = l := by simp [negate]

/-- Evaluate a literal under a Boolean assignment. -/
def eval (l : Literal α) (x : α → Bool) : Bool := x l.atom == l.polarity

@[simp] theorem eval_pos (a : α) (x : α → Bool) : (pos a).eval x = x a := by simp [eval]

@[simp] theorem eval_neg (a : α) (x : α → Bool) : (neg a).eval x = !x a := by simp [eval]

@[simp] theorem eval_map (f : α → β) (l : Literal α) (x : β → Bool) :
    (l.map f).eval x = l.eval (x ∘ f) := rfl

@[simp] theorem eval_negate (l : Literal α) (x : α → Bool) :
    l.negate.eval x = !l.eval x := by
  cases l with
  | mk a p => cases p <;> simp [eval, negate]

@[simp] theorem eval_eq_true (l : Literal α) (x : α → Bool) :
    l.eval x = true ↔ x l.atom = l.polarity := by simp [eval]

end Literal

/-- A clause is a disjunction of its literal occurrences. -/
abbrev Clause (α : Type*) := List (Literal α)

end CNF

/-- A conjunctive normal form is a conjunction of its clause occurrences. -/
abbrev CNF (α : Type*) := List (CNF.Clause α)

namespace CNF

variable {α β : Type*}

/-- Evaluate all clauses under the same assignment. -/
def eval (f : CNF α) (x : α → Bool) : Bool :=
  f.all fun clause => clause.any fun l => l.eval x

@[simp] theorem eval_nil (x : α → Bool) : eval ([] : CNF α) x = true := rfl

@[simp] theorem eval_cons (clause : Clause α) (f : CNF α) (x : α → Bool) :
    eval (clause :: f) x = (clause.any (fun l => l.eval x) && f.eval x) := rfl

@[simp] theorem eval_append (f g : CNF α) (x : α → Bool) :
    (f ++ g).eval x = (f.eval x && g.eval x) := by simp [eval]

theorem eval_eq_true (f : CNF α) (x : α → Bool) :
    f.eval x = true ↔ ∀ clause ∈ f, ∃ l ∈ clause, x l.atom = l.polarity := by
  simp [eval, List.all_eq_true, List.any_eq_true]

@[simp] theorem eval_map (f : CNF α) (r : α → β) (x : β → Bool) :
    eval (f.map (List.map (Literal.map r))) x = f.eval (x ∘ r) := by
  simp [eval, Function.comp_def]

/-- Evaluation depends only on the variables occurring in the formula. -/
theorem eval_congr (f : CNF α) (x y : α → Bool)
    (h : ∀ clause ∈ f, ∀ l ∈ clause, x l.atom = y l.atom) : f.eval x = f.eval y := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true]
  constructor <;> intro hx clause hc
  · obtain ⟨l, hl, hv⟩ := hx clause hc
    exact ⟨l, hl, (h clause hc l hl).symm.trans hv⟩
  · obtain ⟨l, hl, hv⟩ := hx clause hc
    exact ⟨l, hl, (h clause hc l hl).trans hv⟩

/-- The variables of the literal occurrences of a formula, in order and with repetitions. -/
def atoms (f : CNF α) : List α := f.flatMap (List.map Literal.atom)

theorem mem_atoms {f : CNF α} {a : α} : a ∈ f.atoms ↔ ∃ clause ∈ f, ∃ l ∈ clause, l.atom = a := by
  simp [atoms]

end CNF

end Complexity
