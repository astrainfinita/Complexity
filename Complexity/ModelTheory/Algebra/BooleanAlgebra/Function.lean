/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic

/-!
# Boolean functions as terms

Constants, variable literals, finite joins and meets over a list, the selection by a one-hot family
of variables, a three-way branch on two exclusive conditions, and the Shannon expansion of a Boolean
function along a list of variables. Every function of finitely many Boolean variables is the
realization of its expansion; the expansion has size exponential in the number of variables and
shares nothing.
-/

@[expose] public section

namespace FirstOrder.BooleanAlgebra

open Language

variable {α β : Type*}

/-- The constant term with the given truth value. -/
def ofBool (b : Bool) : booleanAlgebra.Term α := if b then ⊤ else ⊥

@[simp] theorem realize_ofBool (b : Bool) (v : α → Bool) :
    (ofBool b : booleanAlgebra.Term α).realize v = b := by
  cases b <;> simp [ofBool]

@[simp] theorem numFuncs_ofBool (b : Bool) : (ofBool b : booleanAlgebra.Term α).numFuncs = 1 := by
  cases b <;> simp [ofBool]

/-- The literal requiring variable `a` to take the value `b`. -/
def literal (a : α) (b : Bool) : booleanAlgebra.Term α :=
  if b then .var a else (.var a)ᶜ

@[simp] theorem realize_literal (a : α) (b : Bool) (v : α → Bool) :
    (literal a b).realize v = (v a == b) := by
  cases b <;> cases h : v a <;> simp [literal, h]

theorem numFuncs_literal_le (a : α) (b : Bool) : (literal a b).numFuncs ≤ 1 := by
  cases b <;> simp [literal]

/-- The join of one term for each list entry; the empty join is `⊥`. -/
def listSup (l : List β) (t : β → booleanAlgebra.Term α) : booleanAlgebra.Term α :=
  l.foldr (fun b s ↦ t b ⊔ s) ⊥

@[simp] theorem realize_listSup (l : List β) (t : β → booleanAlgebra.Term α) (v : α → Bool) :
    (listSup l t).realize v = l.any fun b ↦ (t b).realize v := by
  induction l with
  | nil => simp [listSup]
  | cons b l ih => simp_all [listSup]

@[simp] theorem numFuncs_listSup (l : List β) (t : β → booleanAlgebra.Term α) :
    (listSup l t).numFuncs = (l.map fun b ↦ (t b).numFuncs + 1).sum + 1 := by
  induction l with
  | nil => simp [listSup]
  | cons b l ih =>
    simp only [listSup, List.foldr_cons, numFuncs_sup, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- The meet of one term for each list entry; the empty meet is `⊤`. -/
def listInf (l : List β) (t : β → booleanAlgebra.Term α) : booleanAlgebra.Term α :=
  l.foldr (fun b s ↦ t b ⊓ s) ⊤

@[simp] theorem realize_listInf (l : List β) (t : β → booleanAlgebra.Term α) (v : α → Bool) :
    (listInf l t).realize v = l.all fun b ↦ (t b).realize v := by
  induction l with
  | nil => simp [listInf]
  | cons b l ih => simp_all [listInf]

@[simp] theorem numFuncs_listInf (l : List β) (t : β → booleanAlgebra.Term α) :
    (listInf l t).numFuncs = (l.map fun b ↦ (t b).numFuncs + 1).sum + 1 := by
  induction l with
  | nil => simp [listInf]
  | cons b l ih =>
    simp only [listInf, List.foldr_cons, numFuncs_inf, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem numFuncs_listInf_le {k : ℕ} (l : List β) (t : β → booleanAlgebra.Term α)
    (h : ∀ b ∈ l, (t b).numFuncs ≤ k) :
    (listInf l t).numFuncs ≤ l.length * (k + 1) + 1 := by
  induction l with
  | nil => simp [listInf]
  | cons b l ih =>
    simp only [listInf, List.foldr_cons, numFuncs_inf, List.length_cons, Nat.add_mul,
      Nat.one_mul] at ih ⊢
    have := h b List.mem_cons_self
    have := ih fun c hc ↦ h c (List.mem_cons_of_mem b hc)
    omega

/-- Select the term of the one entry whose selector variable is set. -/
def oneHot (l : List β) (sel : β → α) (t : β → booleanAlgebra.Term α) : booleanAlgebra.Term α :=
  listSup l fun b ↦ .var (sel b) ⊓ t b

theorem realize_oneHot [DecidableEq β] {l : List β} {b₀ : β} (hb : b₀ ∈ l) {sel : β → α}
    {v : α → Bool} (hhot : ∀ b, v (sel b) = decide (b₀ = b)) (t : β → booleanAlgebra.Term α) :
    (oneHot l sel t).realize v = (t b₀).realize v := by
  rw [Bool.eq_iff_iff]
  simp [oneHot, hhot, hb]

@[simp] theorem numFuncs_oneHot (l : List β) (sel : β → α) (t : β → booleanAlgebra.Term α) :
    (oneHot l sel t).numFuncs = (l.map fun b ↦ (t b).numFuncs + 2).sum + 1 := by
  simp only [oneHot, numFuncs_listSup, numFuncs_inf, Term.numFuncs_var, Nat.zero_add,
    Nat.add_assoc]

/-- Branch on two conditions that are never both true: `t₁` under `c₁`, `t₂` under `c₂`, and `t₀`
otherwise. -/
def branch (c₁ c₂ t₁ t₂ t₀ : booleanAlgebra.Term α) : booleanAlgebra.Term α :=
  (c₁ ⊓ t₁) ⊔ (c₂ ⊓ t₂) ⊔ ((c₁ ⊔ c₂)ᶜ ⊓ t₀)

section

variable {c₁ c₂ t₁ t₂ t₀ : booleanAlgebra.Term α} {v : α → Bool}

theorem realize_branch_left (h₁ : c₁.realize v = true) (h₂ : c₂.realize v = false) :
    (branch c₁ c₂ t₁ t₂ t₀).realize v = t₁.realize v := by
  simp [branch, h₁, h₂]

theorem realize_branch_right (h₁ : c₁.realize v = false) (h₂ : c₂.realize v = true) :
    (branch c₁ c₂ t₁ t₂ t₀).realize v = t₂.realize v := by
  simp [branch, h₁, h₂]

theorem realize_branch_else (h₁ : c₁.realize v = false) (h₂ : c₂.realize v = false) :
    (branch c₁ c₂ t₁ t₂ t₀).realize v = t₀.realize v := by
  simp [branch, h₁, h₂]

end

@[simp] theorem numFuncs_branch (c₁ c₂ t₁ t₂ t₀ : booleanAlgebra.Term α) :
    (branch c₁ c₂ t₁ t₂ t₀).numFuncs =
      2 * c₁.numFuncs + 2 * c₂.numFuncs + t₁.numFuncs + t₂.numFuncs + t₀.numFuncs + 7 := by
  simp only [branch, numFuncs_sup, numFuncs_inf, numFuncs_compl]
  omega

/-- Branch on each listed variable in turn; unlisted variables are read as `false`. -/
def shannon [DecidableEq α] : List α → ((α → Bool) → Bool) → booleanAlgebra.Term α
  | [], f => ofBool (f fun _ ↦ false)
  | a :: l, f =>
      (Term.var a ⊓ shannon l fun x ↦ f (Function.update x a true)) ⊔
        ((Term.var a)ᶜ ⊓ shannon l fun x ↦ f (Function.update x a false))

theorem realize_shannon [DecidableEq α] (l : List α) (f : (α → Bool) → Bool) (v : α → Bool) :
    (shannon l f).realize v = f fun a ↦ if a ∈ l then v a else false := by
  induction l generalizing f with
  | nil => simp [shannon]
  | cons a l ih =>
    have h : Function.update (fun c ↦ if c ∈ l then v c else false) a (v a) =
        fun c ↦ if c ∈ a :: l then v c else false := by
      funext c
      by_cases hc : c = a
      · subst hc; simp
      · simp [hc]
    simp only [shannon, realize_sup, realize_inf, realize_compl, Term.realize_var, ih, ← h]
    cases v a <;> simp

/-- A list containing every variable expands a function without changing it. -/
theorem realize_shannon_of_mem [DecidableEq α] {l : List α} (hl : ∀ a, a ∈ l)
    (f : (α → Bool) → Bool) (v : α → Bool) : (shannon l f).realize v = f v := by
  simp [realize_shannon, hl]

/-- The expansion along `l` has `5 * 2 ^ l.length - 4` function symbols. -/
theorem numFuncs_shannon [DecidableEq α] (l : List α) (f : (α → Bool) → Bool) :
    (shannon l f).numFuncs + 4 = 5 * 2 ^ l.length := by
  induction l generalizing f with
  | nil => simp [shannon]
  | cons a l ih =>
    simp only [shannon, numFuncs_sup, numFuncs_inf, numFuncs_compl, Term.numFuncs_var,
      List.length_cons, pow_succ]
    have h₁ := ih fun x ↦ f (Function.update x a true)
    have h₂ := ih fun x ↦ f (Function.update x a false)
    omega

end FirstOrder.BooleanAlgebra
