/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Bounds
public import Complexity.Encoding.Prod

/-! # Telling constructors apart by their codes

A `CaseTree` decides the constructor of a value from its code by tests of the roots of subtrees,
and finds the code of the constructor's fields as a subtree. One program runs every such decision,
so its correctness is proved once. A `CaseView` of a type gives its constructors, their fields and
the decision on their codes, a description of the encoding that `@[tree_encoding]` derives with
it.
-/

@[expose] public section

universe u

namespace Complexity.TreeProgram

namespace Expr

/-- The expression for the subtree at a path. -/
def subtree (e : Expr ℕ) : List Bool → Expr ℕ
  | [] => e
  | r :: path => (if r then right e else left e).subtree path

@[simp] theorem eval_subtree (e : Expr ℕ) (path : List Bool) (s : ℕ → Tree) :
    (e.subtree path).eval s = (e.eval s).subtree path := by
  induction path generalizing e with
  | nil => rfl
  | cons r path ih => cases r <;> simp [subtree, Tree.subtree, ih]

@[simp] theorem maxSize_subtree (e : Expr ℕ) (path : List Bool) (s : ℕ → Tree) :
    (e.subtree path).maxSize s = e.maxSize s := by
  induction path generalizing e with
  | nil => rfl
  | cons r path ih => cases r <;> simp [subtree, ih]

theorem steps_subtree (e : Expr ℕ) (path : List Bool) :
    (e.subtree path).steps = e.steps + path.length := by
  induction path generalizing e with
  | nil => rfl
  | cons r path ih => cases r <;> simp [subtree, ih] <;> omega

theorem assignSteps_subtree_le (v : Value) (path : List Bool) :
    (v.expression.subtree path).assignSteps ≤ path.length + 2 := by
  cases path with
  | nil => exact v.assignSteps_le.trans (by omega)
  | cons r path =>
    have h (e : Expr ℕ) (r : Bool) : ((if r then right e else left e).subtree path).assignSteps =
        e.steps + path.length + 1 := by
      induction path generalizing e r with
      | nil => cases r <;> simp [subtree]
      | cons r' path ih => cases r <;> simp only [subtree, ih] <;> simp <;> omega
    simp only [subtree, h]
    cases v <;> simp

end Expr

/-- A decision on the code of a value: tests of the roots of subtrees select a constructor, whose
fields have the subtree at the leaf's path as their code. -/
inductive CaseTree (k : ℕ) where
  | leaf (i : Fin k) (path : List Bool)
  | test (path : List Bool) (yes no : CaseTree k)

namespace CaseTree

variable {k : ℕ}

/-- The constructor, and the code of its fields, the decision selects on a code. -/
def select : CaseTree k → Tree → Fin k × Tree
  | leaf i path, t => (i, t.subtree path)
  | test path yes no, t => if (t.subtree path).root then yes.select t else no.select t

/-- Run the decision on a computed code, continuing with the selected handler at the fields. -/
def run : CaseTree k → Value → (Fin k → Value → Code Value) → Code Value
  | leaf i path, w, h => do let a ← Code.eval (w.expression.subtree path); h i a
  | test path yes no, w, h => Code.branch (w.expression.subtree path) (yes.run w h) (no.run w h)

/-- A bound on the steps of the decision, apart from the handler. -/
def cost : CaseTree k → ℕ
  | leaf _ path => path.length + 2
  | test path yes no => path.length + 3 + max yes.cost no.cost

theorem run_fresh (D : CaseTree k) {w : Value} {h : Fin k → Value → Code Value}
    (hh : ∀ i a m, a.expression.bound ≤ m →
      m ≤ ((h i a).build m).2.1 ∧ ((h i a).build m).1.expression.bound ≤ ((h i a).build m).2.1)
    {n : ℕ} (hw : w.expression.bound ≤ n) :
    n ≤ ((D.run w h).build n).2.1 ∧
      ((D.run w h).build n).1.expression.bound ≤ ((D.run w h).build n).2.1 := by
  induction D generalizing n with
  | leaf i path =>
    have := hh i (.var n) (n + 1) le_rfl
    simp only [run, Code.build_bind, Code.eval_build]
    exact ⟨(Nat.le_succ n).trans this.1, this.2⟩
  | test path yes no ihy _ =>
    have := ihy (n := n + 1) (by omega)
    simp only [run, Code.branch_build, Code.build_bind, Code.write_build]
    exact ⟨(Nat.le_succ n).trans (this.1.trans (le_max_left _ _)),
      this.1.trans (le_max_left _ _)⟩

/-- The decision runs the handler selected on the code, at a value whose code is the selected
subtree, within the handler's budget and the decision's cost. -/
theorem run_bounded (D : CaseTree k) {w : Value} {h : Fin k → Value → Code Value} {n : ℕ}
    {s : ℕ → Tree} (hw : w.expression.bound ≤ n) {time space : ℕ} {Y : Tree}
    (hsize : (w.eval s).size ≤ space) (hY : Y.size ≤ space)
    (hh : ∀ m t a, n ≤ m → a.expression.bound ≤ m → (∀ j < n, t j = s j) →
      a.eval t = (D.select (w.eval s)).2 →
      (h (D.select (w.eval s)).1 a).Bounded m t time space
        (fun r u => r.eval u = Y ∧ ∀ j < m, u j = t j)) :
    (D.run w h).Bounded n s (time + D.cost) space
      (fun r u => r.eval u = Y ∧ ∀ j < n, u j = s j) := by
  induction D generalizing n with
  | leaf i path =>
    have := Expr.assignSteps_subtree_le w path
    simp only [run, Code.bounded_eval_bind_iff, Expr.maxSize_subtree, Value.maxSize_expression]
    refine ⟨by simp [cost]; omega, hsize, ?_⟩
    apply (hh (n + 1) _ (.var n) (by omega) le_rfl (fun j hj => by simp [Nat.ne_of_lt hj])
      (by simp [select])).mono (by simp [cost]; omega) le_rfl
    intro r u ⟨hr, hu⟩
    exact ⟨hr, fun j hj => (hu j (by omega)).trans (by simp [Nat.ne_of_lt hj])⟩
  | test path yes no ihy ihn =>
    have branch {D' : CaseTree k} (hD : D'.select (w.eval s) = (test path yes no).select (w.eval s))
        (ih : (∀ m t a, n + 1 ≤ m → a.expression.bound ≤ m → (∀ j < n + 1, t j = s j) →
          a.eval t = (D'.select (w.eval s)).2 →
          (h (D'.select (w.eval s)).1 a).Bounded m t time space
            (fun r u => r.eval u = Y ∧ ∀ j < m, u j = t j)) →
          (D'.run w h).Bounded (n + 1) s (time + D'.cost) space
            (fun r u => r.eval u = Y ∧ ∀ j < n + 1, u j = s j))
        (hc : D'.cost ≤ max yes.cost no.cost) :
        (D'.run w h).Bounded (n + 1) s (time + max yes.cost no.cost) space
          (fun v t => (v.eval t).size ≤ space ∧
            (Value.var n).eval (Function.update t n (v.eval t)) = Y ∧
            ∀ j < n, Function.update t n (v.eval t) j = s j) := by
      apply (ih fun m t a hm ha ht hat => by
        rw [hD] at hat ⊢
        exact hh m t a (by omega) ha (fun j hj => ht j (by omega)) hat).mono (by omega) le_rfl
      intro r u ⟨hr, hu⟩
      exact ⟨hr ▸ hY, by simp [hr], fun j hj => by simp [Nat.ne_of_lt hj, hu j (by omega)]⟩
    have := Code.Bounded.branch (w.expression.subtree path) (yes.run w h) (no.run w h)
      (fun r u => r.eval u = Y ∧ ∀ j < n, u j = s j) (by cases w <;> simpa using hsize)
      (fun hr => branch
        (by simp only [Expr.eval_subtree, Value.eval_expression] at hr; simp [select, hr])
        (ihy (by omega)) (le_max_left _ _))
      (fun hr => branch
        (by simp only [Expr.eval_subtree, Value.eval_expression] at hr; simp [select, hr])
        (ihn (by omega)) (le_max_right _ _))
    rw [Expr.steps_subtree] at this
    exact this.mono (by cases w <;> simp [cost] <;> omega) le_rfl (fun _ _ h => h)

end CaseTree

/-- A type viewed as the constructors of its matches: each value is `ofPayload i p` for a
constructor `i` and the tuple `p` of its fields, and a decision on the code of `ofPayload i p`
selects `i` and the code of `p`. `elim` states a quantity by constructor, as a `match`. -/
class CaseView (T : Type u) [UniqueEncoding Tree T] (k : outParam ℕ) where
  /-- The tuple of fields of each constructor. -/
  Payload : Fin k → Type u
  [encoding : ∀ i, UniqueEncoding Tree (Payload i)]
  /-- The value of a constructor at its fields. -/
  ofPayload : (i : Fin k) → Payload i → T
  exists_ofPayload : ∀ t, ∃ i p, ofPayload i p = t
  /-- A quantity by constructor, as a `match` with the value's equation. -/
  elim : (t : T) → ((i : Fin k) → (p : Payload i) → t = ofPayload i p → ℕ) → ℕ
  elim_ofPayload : ∀ i p g, elim (ofPayload i p) g = g i p rfl
  /-- The decision on codes. -/
  dispatch : CaseTree k
  select_encode : ∀ i p, dispatch.select ⌜ofPayload i p⌝ₜ = (i, ⌜p⌝ₜ)

attribute [instance_reducible, instance] CaseView.encoding

namespace CaseView

variable {k : ℕ}

theorem elim_eq {T : Type u} [UniqueEncoding Tree T] [CaseView T k] {t : T}
    (g : (i : Fin k) → (p : Payload T i) → t = ofPayload i p → ℕ) {i : Fin k} {p : Payload T i}
    (h : t = ofPayload i p) : elim t g = g i p h := by
  subst h
  exact elim_ofPayload i p g

end CaseView

end Complexity.TreeProgram
