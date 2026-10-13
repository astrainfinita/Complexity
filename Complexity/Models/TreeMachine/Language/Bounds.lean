/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Verification
public import Complexity.Models.TreeMachine.Language.Closure

/-! # Source time and intermediate-tree bounds

`Bounded` is a total-correctness contract for the same source execution as `Exec`.
Time adds under composition; one uniform bound covers all evaluated subexpressions.
The compiler accounts separately for initial values, retained locals and copy temporaries.
-/

@[expose] public section

namespace Complexity.TreeProgram

namespace Cmd

variable {ν : Type} [DecidableEq ν] {p q : Cmd ν} {s t : ν → Tree} {n b : ℕ}

@[simp] theorem run_skip_iff : (skip : Cmd ν).Run s n t b ↔ n = 0 ∧ t = s ∧ b = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .skip _

@[simp] theorem run_assign_iff (x : ν) (e : Expr ν) :
    (assign x e).Run s n t b ↔
      n = e.assignSteps ∧ t = Function.update s x (e.eval s) ∧ b = e.maxSize s := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .assign x e s

@[simp] theorem run_seq_skip_iff : (seq p skip).Run s n t b ↔ p.Run s n t b := by
  constructor
  · intro h; cases h with
    | seq hp hq => cases hq; simpa using hp
  · intro h; simpa using Run.seq h (.skip t)

/-- Total correctness with a transition budget and a bound on evaluated tree values. -/
def Bounded (p : Cmd ν) (s : ν → Tree) (time space : ℕ) (Q : (ν → Tree) → Prop) : Prop :=
  ∃ n t b, p.Run s n t b ∧ n ≤ time ∧ b ≤ space ∧ Q t

@[simp] theorem bounded_assign_iff (x : ν) (e : Expr ν) (Q : (ν → Tree) → Prop)
    (time space : ℕ) :
    (assign x e).Bounded s time space Q ↔
      e.assignSteps ≤ time ∧ e.maxSize s ≤ space ∧ Q (Function.update s x (e.eval s)) := by
  simp [Bounded]

@[simp] theorem bounded_seq_skip_iff (Q : (ν → Tree) → Prop) (time space : ℕ) :
    (seq p skip).Bounded s time space Q ↔ p.Bounded s time space Q := by
  simp [Bounded]

/-- A branch spends the test budget, then executes only the selected arm. -/
@[simp] theorem bounded_branch_iff (e : Expr ν) (Q : (ν → Tree) → Prop) (time space : ℕ) :
    (branch e p q).Bounded s time space Q ↔
      e.steps + 1 ≤ time ∧ e.maxSize s ≤ space ∧
      (if (e.eval s).root then p else q).Bounded s (time - (e.steps + 1)) space Q := by
  constructor
  · rintro ⟨n, t, b, hr, hn, hb, hQ⟩
    cases hr with
    | branch_true he hp =>
      refine ⟨by omega, by omega, ?_⟩
      simp only [he, ↓reduceIte]
      exact ⟨_, _, _, hp, by omega, by omega, hQ⟩
    | branch_false he hq =>
      refine ⟨by omega, by omega, ?_⟩
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, _, _, hq, by omega, by omega, hQ⟩
  · rintro ⟨ht, hs, n, t, b, hr, hn, hb, hQ⟩
    cases he : (e.eval s).root with
    | true => exact ⟨_, _, _, .branch_true he (by simpa [he] using hr), by omega,
        Nat.max_le.mpr ⟨hs, hb⟩, hQ⟩
    | false => exact ⟨_, _, _, .branch_false he (by simpa [he] using hr), by omega,
        Nat.max_le.mpr ⟨hs, hb⟩, hQ⟩

/-- An assignment spends its exact local budget before the rest of the source block. -/
theorem bounded_assign_seq_iff (x : ν) (e : Expr ν) (Q : (ν → Tree) → Prop)
    (time space : ℕ) :
    (seq (assign x e) p).Bounded s time space Q ↔
      e.assignSteps ≤ time ∧ e.maxSize s ≤ space ∧
      p.Bounded (Function.update s x (e.eval s)) (time - e.assignSteps) space Q := by
  constructor
  · rintro ⟨n, t, b, hr, hn, hb, hQ⟩
    cases hr with
    | seq he hp =>
      cases he
      exact ⟨by omega, by omega, _, _, _, hp, by omega, by omega, hQ⟩
  · rintro ⟨ht, hs, n, t, b, hr, hn, hb, hQ⟩
    exact ⟨_, t, _, .seq (.assign x e s) hr, by omega, Nat.max_le.mpr ⟨hs, hb⟩, hQ⟩

namespace Bounded

variable {time space : ℕ} {Q R : (ν → Tree) → Prop}

theorem mono (h : p.Bounded s time space Q) {time' space' : ℕ}
    (ht : time ≤ time') (hs : space ≤ space') (hQ : ∀ t, Q t → R t) :
    p.Bounded s time' space' R := by
  obtain ⟨n, t, b, hr, hn, hb, hq⟩ := h
  exact ⟨n, t, b, hr, Nat.le_trans hn ht, Nat.le_trans hb hs, hQ t hq⟩

theorem exec (h : p.Bounded s time space Q) : ∃ t, p.Exec s t ∧ Q t := by
  obtain ⟨n, t, b, hr, _, _, hq⟩ := h
  exact ⟨t, ⟨n, b, hr⟩, hq⟩

theorem seq {a b : ℕ} (hp : p.Bounded s a space Q)
    (hq : ∀ t, Q t → q.Bounded t b space R) : (Cmd.seq p q).Bounded s (a + b) space R := by
  obtain ⟨n, t, c, hp, hn, hc, hQ⟩ := hp
  obtain ⟨m, u, d, hq, hm, hd, hR⟩ := hq t hQ
  exact ⟨n + m, u, max c d, .seq hp hq, Nat.add_le_add hn hm, Nat.max_le.mpr ⟨hc, hd⟩, hR⟩

/-- Spend the remaining credit on the final command as well as the loop itself. -/
theorem loop_budget_seq (e : Expr ν) (I : (ν → Tree) → ℕ → Prop) (budget : ℕ)
    (hs : I s budget) (he : ∀ s k, I s k → e.maxSize s ≤ space)
    (stop : ∀ s k, I s k → (e.eval s).root = false →
      e.steps + 2 ≤ k ∧ q.Bounded s (k - (e.steps + 2)) space Q)
    (body : ∀ s k, I s k → (e.eval s).root = true →
      ∃ bodyTime, p.Bounded s bodyTime space (fun t =>
        ∃ remaining, I t remaining ∧ bodyTime + e.steps + 2 + remaining ≤ k)) :
    (Cmd.seq (.while e p) q).Bounded s budget space Q := by
  induction budget using Nat.strong_induction_on generalizing s with
  | h budget ih =>
    cases hr : (e.eval s).root with
    | false =>
      obtain ⟨ht, n, t, b, hq, hn, hb, hQ⟩ := stop s budget hs hr
      exact ⟨_, t, _, .seq (.while_false hr) hq, by omega,
        max_le (he s budget hs) hb, hQ⟩
    | true =>
      obtain ⟨bodyTime, a, t, c, hp, ha, hc, remaining, ht, hbudget⟩ := body s budget hs hr
      obtain ⟨b, u, d, hu, hb, hd, hQ⟩ := ih remaining (by omega) ht
      cases hu with
      | seq hw hq =>
        exact ⟨_, u, _, .seq (.while_true hr hp hw) hq, by omega,
          by simpa only [max_le_iff] using
            And.intro (And.intro (he s budget hs) (And.intro hc (max_le_iff.mp hd).1))
              (max_le_iff.mp hd).2, hQ⟩

/-- A loop spends a remaining budget. Each successful iteration pays for its test,
body and back edge; the final failed test is included in the invariant. -/
theorem loop_budget (e : Expr ν) (I : (ν → Tree) → ℕ → Prop) (budget : ℕ)
    (hs : I s budget) (he : ∀ s k, I s k → e.maxSize s ≤ space)
    (stop : ∀ s k, I s k → (e.eval s).root = false → e.steps + 2 ≤ k)
    (body : ∀ s k, I s k → (e.eval s).root = true →
      ∃ bodyTime, p.Bounded s bodyTime space (fun t =>
        ∃ remaining, I t remaining ∧ bodyTime + e.steps + 2 + remaining ≤ k)) :
    (Cmd.while e p).Bounded s budget space
      (fun t => (∃ remaining, I t remaining) ∧ (e.eval t).root = false) := by
  rw [← bounded_seq_skip_iff]
  apply loop_budget_seq e I budget hs he ?_ body
  intro t k hi hr
  exact ⟨stop t k hi hr, 0, t, 0, .skip t, Nat.zero_le _, Nat.zero_le _, ⟨k, hi⟩, hr⟩

/-- A decreasing measure gives a loop bound from a uniform per-iteration budget.
The final failed test is included, and space does not accumulate across iterations. -/
theorem loop (e : Expr ν) (I : (ν → Tree) → Prop) (measure : (ν → Tree) → ℕ)
    (bodyTime : ℕ) (hs : I s) (he : ∀ s, I s → e.maxSize s ≤ space)
    (body : ∀ s, I s → (e.eval s).root = true →
      p.Bounded s bodyTime space (fun t ↦ I t ∧ measure t < measure s)) :
    (Cmd.while e p).Bounded s ((bodyTime + e.steps + 2) * measure s + (e.steps + 2)) space
      (fun t ↦ I t ∧ (e.eval t).root = false) := by
  let budget t := (bodyTime + e.steps + 2) * measure t + (e.steps + 2)
  apply (loop_budget e (fun t k => I t ∧ budget t ≤ k) (budget s)
    ⟨hs, le_rfl⟩ (fun t k ht => he t ht.1) ?_ ?_).mono le_rfl le_rfl
  · rintro t ⟨⟨k, hi, _⟩, hr⟩; exact ⟨hi, hr⟩
  · intro t k ht _
    exact (Nat.le_add_left _ _).trans ht.2
  · intro t k ht hr
    refine ⟨bodyTime, (body t ht.1 hr).mono le_rfl le_rfl ?_⟩
    rintro u ⟨hu, hm⟩
    refine ⟨budget u, ⟨hu, le_rfl⟩, ?_⟩
    have hmul := Nat.mul_le_mul_left (bodyTime + e.steps + 2)
      (show measure u + 1 ≤ measure t by omega)
    dsimp [budget] at ht ⊢
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

end Bounded
end Cmd

@[simp] theorem Value.maxSize_expression (v : Value) (s : ℕ → Tree) :
    v.expression.maxSize s = (v.eval s).size := by cases v <;> rfl

@[simp] theorem Value.steps_expression (v : Value) : v.expression.steps = 0 := by
  cases v <;> rfl

/-- Allocating a fresh source name cannot change an already available value. -/
theorem Value.eval_update_of_bound_le (v : Value) {n : ℕ} (h : v.expression.bound ≤ n)
    (s : ℕ → Tree) (x : Tree) : v.eval (Function.update s n x) = v.eval s := by
  cases v with
  | nil => rfl
  | var j =>
    have hj : j ≠ n := by change j + 1 ≤ n at h; omega
    simp [Value.eval, hj]

/-- A helper preserving earlier source locations also preserves the values stored there. -/
theorem Value.eval_eq_of_forall_lt (v : Value) {n : ℕ} (h : v.expression.bound ≤ n)
    {s t : ℕ → Tree} (hs : ∀ j < n, t j = s j) : v.eval t = v.eval s := by
  cases v with
  | nil => rfl
  | var j => exact hs j (by change j + 1 ≤ n at h; omega)

theorem Value.assignSteps_le (v : Value) : v.expression.assignSteps ≤ 2 := by
  cases v <;> simp

namespace Code

variable {α β : Type} {n time space : ℕ} {s : ℕ → Tree}

/-- A source contract with unit-time and intermediate-tree budgets; no physical slots occur. -/
def Bounded (p : Code α) (n : ℕ) (s : ℕ → Tree) (time space : ℕ)
    (Q : α → (ℕ → Tree) → Prop) : Prop :=
  (block (p.build n).2.2).Bounded s time space (Q (p.build n).1)

private theorem run_block_append {cs ds : List (Cmd ℕ)} {s t u : ℕ → Tree} {n m a b : ℕ}
    (hp : (block cs).Run s n t a) (hq : (block ds).Run t m u b) :
    (block (cs ++ ds)).Run s (n + m) u (max a b) := by
  induction cs generalizing s n a with
  | nil => cases hp; simpa using hq
  | cons c cs ih =>
    cases hp with
    | seq hc ht => simpa [block, Nat.add_assoc, Nat.max_assoc] using Cmd.Run.seq hc (ih ht)

@[simp] theorem bounded_pure_iff (a : α) (Q : α → (ℕ → Tree) → Prop) :
    (pure a : Code α).Bounded n s time space Q ↔ Q a s := by
  simp [Bounded, Cmd.Bounded, block]

@[simp] theorem bounded_eval_iff (e : Expr ℕ) (Q : Value → (ℕ → Tree) → Prop) :
    (eval e).Bounded n s time space Q ↔ e.assignSteps ≤ time ∧ e.maxSize s ≤ space ∧
      Q (.var n) (Function.update s n (e.eval s)) := by
  simp [Bounded, block]

@[simp] theorem bounded_newVar_iff (v : Value) (Q : Var → (ℕ → Tree) → Prop) :
    (newVar v).Bounded n s time space Q ↔ v.expression.assignSteps ≤ time ∧
      (v.eval s).size ≤ space ∧ Q ⟨n⟩ (Function.update s n (v.eval s)) := by
  simp [Bounded, block]

@[simp] theorem bounded_read_iff (v : Var) (Q : Value → (ℕ → Tree) → Prop) :
    (read v).Bounded n s time space Q ↔ 2 ≤ time ∧ (v.get s).size ≤ space ∧
      Q (.var n) (Function.update s n (v.get s)) := by
  simp [read, Var.get]

@[simp] theorem bounded_write_iff (v : Var) (a : Value) (Q : Unit → (ℕ → Tree) → Prop) :
    (write v a).Bounded n s time space Q ↔ a.expression.assignSteps ≤ time ∧
      (a.eval s).size ≤ space ∧ Q () (Function.update s v.index (a.eval s)) := by
  simp [Bounded, block]

@[simp↓] theorem bounded_eval_bind_iff (e : Expr ℕ) (f : Value → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (eval e >>= f).Bounded n s time space Q ↔ e.assignSteps ≤ time ∧ e.maxSize s ≤ space ∧
      (f (.var n)).Bounded (n + 1) (Function.update s n (e.eval s))
        (time - e.assignSteps) space Q := by
  simp only [Bounded, build_bind, eval_build, List.singleton_append, block,
    Cmd.bounded_assign_seq_iff]

@[simp↓] theorem bounded_read_bind_iff (v : Var) (f : Value → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (read v >>= f).Bounded n s time space Q ↔ 2 ≤ time ∧ (v.get s).size ≤ space ∧
      (f (.var n)).Bounded (n + 1) (Function.update s n (v.get s)) (time - 2) space Q := by
  simp [read, Var.get]

-- Apply the contracts before the simp definitions of the corresponding value operations.
@[simp↓] theorem bounded_left_bind_iff (v : Value) (f : Value → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (v.left >>= f).Bounded n s time space Q ↔ 1 ≤ time ∧ (v.eval s).size ≤ space ∧
      (f (.var n)).Bounded (n + 1) (Function.update s n (v.eval s).left) (time - 1) space Q := by
  simp

@[simp↓] theorem bounded_right_bind_iff (v : Value) (f : Value → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (v.right >>= f).Bounded n s time space Q ↔ 1 ≤ time ∧ (v.eval s).size ≤ space ∧
      (f (.var n)).Bounded (n + 1) (Function.update s n (v.eval s).right) (time - 1) space Q := by
  simp

@[simp↓] theorem bounded_pair_bind_iff (a b : Value) (f : Value → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (a.pair b >>= f).Bounded n s time space Q ↔
      1 ≤ time ∧ (Tree.pair (a.eval s) (b.eval s)).size ≤ space ∧
      (f (.var n)).Bounded (n + 1) (Function.update s n (.pair (a.eval s) (b.eval s)))
        (time - 1) space Q := by
  simp
  omega

@[simp↓] theorem bounded_newVar_bind_iff (v : Value) (f : Var → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (newVar v >>= f).Bounded n s time space Q ↔
      v.expression.assignSteps ≤ time ∧ (v.eval s).size ≤ space ∧
      (f ⟨n⟩).Bounded (n + 1) (Function.update s n (v.eval s))
        (time - v.expression.assignSteps) space Q := by
  simp only [Bounded, build_bind, newVar_build, List.singleton_append, block,
    Cmd.bounded_assign_seq_iff, Value.maxSize_expression, Value.eval_expression]

@[simp↓] theorem bounded_write_bind_iff (v : Var) (a : Value) (f : Unit → Code α)
    (Q : α → (ℕ → Tree) → Prop) :
    (write v a >>= f).Bounded n s time space Q ↔
      a.expression.assignSteps ≤ time ∧ (a.eval s).size ≤ space ∧
      (f ()).Bounded n (Function.update s v.index (a.eval s))
        (time - a.expression.assignSteps) space Q := by
  simp only [Bounded, build_bind, write_build, List.singleton_append, block,
    Cmd.bounded_assign_seq_iff, Value.maxSize_expression, Value.eval_expression]

@[simp] theorem bounded_branch_iff (e : Expr ℕ) (yes no : Code Value)
    (Q : Value → (ℕ → Tree) → Prop) :
    (branch e yes no).Bounded n s time space Q ↔
      e.steps + 1 ≤ time ∧ e.maxSize s ≤ space ∧
      ((if (e.eval s).root then yes else no) >>= fun a ↦ write ⟨n⟩ a).Bounded
        (n + 1) s (time - (e.steps + 1)) space (fun _ ↦ Q (.var n)) := by
  cases h : (e.eval s).root <;> simp [Bounded, block, h]

namespace Bounded

variable {p : Code α} {f : α → Code β} {Q R : α → (ℕ → Tree) → Prop}

theorem mono (h : p.Bounded n s time space Q) {time' space' : ℕ}
    (ht : time ≤ time') (hs : space ≤ space') (hQ : ∀ a t, Q a t → R a t) :
    p.Bounded n s time' space' R := Cmd.Bounded.mono h ht hs (hQ _)

/-- The returned source value is fixed when the code is built. -/
theorem with_result (h : p.Bounded n s time space Q) :
    p.Bounded n s time space (fun a t => a = (p.build n).1 ∧ Q a t) :=
  Cmd.Bounded.mono h le_rfl le_rfl (fun _ h => ⟨rfl, h⟩)

/-- A returned value is bounded by the initial values and the intermediate-tree budget. -/
theorem with_size_le {p : Code Value} {Q : Value → (ℕ → Tree) → Prop}
    (h : p.Bounded n s time space Q) {bound : ℕ}
    (hs : ∀ j, (s j).size ≤ bound) (hb : space ≤ bound) :
    p.Bounded n s time space (fun v t => Q v t ∧ (v.eval t).size ≤ bound) := by
  obtain ⟨i, t, c, hr, hi, hc, hQ⟩ := h
  refine ⟨i, t, c, hr, hi, hc, hQ, ?_⟩
  have ht := hr.size_le hs (hc.trans hb)
  cases (p.build n).1 with
  | nil => exact (Tree.size_pos (s 0)).trans_le (hs 0)
  | var j => exact ht j

theorem exec (h : p.Bounded n s time space Q) :
    ∃ a m t, p.Exec n s a m t ∧ Q a t := by
  obtain ⟨t, hr, hQ⟩ := Cmd.Bounded.exec h
  exact ⟨_, _, t, ⟨rfl, hr⟩, hQ⟩

theorem bind {a b : ℕ} {R : β → (ℕ → Tree) → Prop}
    (hp : p.Bounded n s a space Q)
    (hf : ∀ v t, Q v t → (f v).Bounded (p.build n).2.1 t b space R) :
    (p >>= f).Bounded n s (a + b) space R := by
  obtain ⟨i, t, c, hp, hi, hc, hQ⟩ := hp
  obtain ⟨j, u, d, hf, hj, hd, hR⟩ := hf _ t hQ
  exact ⟨i + j, u, max c d, run_block_append hp hf,
    Nat.add_le_add hi hj, Nat.max_le.mpr ⟨hc, hd⟩, hR⟩

theorem ifNode (v : Value) (yes no : Code Unit) (Q : Unit → (ℕ → Tree) → Prop)
    (hv : (v.eval s).size ≤ space)
    (hy : (v.eval s).root = true → yes.Bounded n s time space Q)
    (hn : (v.eval s).root = false → no.Bounded n s time space Q) :
    (Code.ifNode v yes no).Bounded n s (1 + time) space Q := by
  simp only [Bounded, ifNode_build, block, Cmd.bounded_seq_skip_iff,
    Cmd.bounded_branch_iff, Value.steps_expression, Value.maxSize_expression,
    Value.eval_expression, Nat.zero_add, Nat.add_sub_cancel_left]
  refine ⟨by omega, hv, ?_⟩
  cases he : (v.eval s).root with
  | false => simpa [he, Bounded] using hn he
  | true => simpa [he, Bounded] using hy he

/-- A returned branch pays for its test and for saving the selected result. -/
theorem branch (e : Expr ℕ) (yes no : Code Value) (Q : Value → (ℕ → Tree) → Prop)
    (he : e.maxSize s ≤ space)
    (hy : (e.eval s).root = true → yes.Bounded (n + 1) s time space
      (fun v t ↦ (v.eval t).size ≤ space ∧ Q (.var n) (Function.update t n (v.eval t))))
    (hn : (e.eval s).root = false → no.Bounded (n + 1) s time space
      (fun v t ↦ (v.eval t).size ≤ space ∧ Q (.var n) (Function.update t n (v.eval t)))) :
    (Code.branch e yes no).Bounded n s (e.steps + 1 + (time + 2)) space Q := by
  rw [bounded_branch_iff]
  refine ⟨by omega, he, ?_⟩
  simp only [Nat.add_sub_cancel_left]
  have h : (if (e.eval s).root then yes else no).Bounded (n + 1) s time space
      (fun v t ↦ (v.eval t).size ≤ space ∧ Q (.var n) (Function.update t n (v.eval t))) := by
    cases hr : (e.eval s).root
    · simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hn hr
    · simpa only [hr, ↓reduceIte] using hy hr
  apply h.bind
  intro v t ⟨hs, hq⟩
  exact bounded_write_iff .. |>.mpr ⟨v.assignSteps_le, hs, hq⟩

/-- A source loop may spend a different body budget on each iteration. -/
theorem whileNode_budget (v : Var) (body : Code Unit) (I : (ℕ → Tree) → ℕ → Prop)
    (budget : ℕ) (hs : I s budget)
    (hv : ∀ s k, I s k → (v.get s).size ≤ space)
    (stop : ∀ s k, I s k → (v.get s).root = false → 2 ≤ k)
    (hb : ∀ s k, I s k → (v.get s).root = true →
      ∃ bodyTime, body.Bounded n s bodyTime space (fun _ t =>
        ∃ remaining, I t remaining ∧ bodyTime + 2 + remaining ≤ k)) :
    (Code.whileNode v body).Bounded n s budget space
      (fun _ t => (∃ remaining, I t remaining) ∧ (v.get t).root = false) := by
  obtain ⟨i, t, b, hr, hi, hb, hQ⟩ := Cmd.Bounded.loop_budget (.var v.index) I budget
    hs hv stop hb
  exact ⟨i, t, b, by simpa [Code.block] using hr, hi, hb, hQ⟩

/-- Bound a source loop using an invariant and a strictly decreasing iteration count. -/
theorem whileNode (v : Var) (body : Code Unit) (I : (ℕ → Tree) → Prop)
    (measure : (ℕ → Tree) → ℕ) (bodyTime : ℕ) (hs : I s)
    (hv : ∀ s, I s → (v.get s).size ≤ space)
    (hb : ∀ s, I s → (v.get s).root = true →
      body.Bounded n s bodyTime space (fun _ t ↦ I t ∧ measure t < measure s)) :
    (Code.whileNode v body).Bounded n s ((bodyTime + 2) * measure s + 2) space
      (fun _ t ↦ I t ∧ (v.get t).root = false) := by
  obtain ⟨i, t, b, hr, hi, hb, hQ⟩ := Cmd.Bounded.loop (.var v.index) I measure bodyTime
    hs hv hb
  exact ⟨i, t, b, by simpa [block] using hr, hi, hb, hQ⟩

end Bounded
end Code
end Complexity.TreeProgram
