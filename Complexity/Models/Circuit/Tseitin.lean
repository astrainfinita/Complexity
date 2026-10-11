/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.CNF.Basic
public import Complexity.Models.Circuit.Basic
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic

/-! # Tseitin constraints for Boolean circuits

Input wires retain their indices; each gate constrains the next fresh variable to its value.
The final unit clause requires the selected output to be true. Correctness preserves any fixed
input assignment, using the standard Boolean interpretation.
-/

@[expose] public section

namespace Complexity

open FirstOrder
open FirstOrder.Language (Structure)

namespace CNF

variable {α : Type*} {k : ℕ}

/-- Clauses asserting that `out` is the result of a Boolean gate on `args`. -/
def ofGate : {k : ℕ} → Language.booleanAlgebra.Functions k → (Fin k → α) → α → CNF α
  | _, .inf, args, out =>
      [ [.neg out, .pos (args 0)], [.neg out, .pos (args 1)],
       [.pos out, .neg (args 0), .neg (args 1)] ]
  | _, .sup, args, out =>
      [ [.pos out, .neg (args 0)], [.pos out, .neg (args 1)],
       [.neg out, .pos (args 0), .pos (args 1)] ]
  | _, .compl, args, out => [ [.pos out, .pos (args 0)], [.neg out, .neg (args 0)] ]
  | _, .bot, _, out => [ [.neg out] ]
  | _, .top, _, out => [ [.pos out] ]

@[simp] theorem eval_ofGate (op : Language.booleanAlgebra.Functions k) (args : Fin k → α)
    (out : α) (x : α → Bool) :
    (ofGate op args out).eval x = (x out == Structure.funMap op (x ∘ args)) := by
  cases op <;> simp [ofGate, eval, Function.comp_def] <;> grind

theorem length_ofGate_le (op : Language.booleanAlgebra.Functions k) (args : Fin k → α) (out : α) :
    (ofGate op args out).length ≤ 3 := by
  cases op <;> simp [ofGate]

theorem ofGate_width (op : Language.booleanAlgebra.Functions k) (args : Fin k → α) (out : α) :
    ∀ clause ∈ ofGate op args out, clause.length ≤ 3 := by
  cases op <;> simp [ofGate]

end CNF

namespace Circuit

/-- Translate a single-output Boolean circuit to a CNF, asserting that its output is true. -/
@[simp] def tseitin : {n : ℕ} → Circuit .booleanAlgebra n 1 → CNF ℕ
  | _, .outputs select => [ [.pos (select 0).val] ]
  | n, .gate op args next => CNF.ofGate op (Fin.val ∘ args) n ++ next.tseitin

/-- Every clause in the Tseitin translation has at most three literals. -/
theorem tseitin_width {n : ℕ} (c : Circuit .booleanAlgebra n 1) :
    ∀ clause ∈ c.tseitin, clause.length ≤ 3 := by
  cases c with
  | outputs select => simp [tseitin]
  | gate op args next =>
      simpa only [tseitin, List.mem_append, or_imp, forall_and] using
        And.intro (CNF.ofGate_width op (Fin.val ∘ args) n) next.tseitin_width
termination_by c.size

/-- Each gate contributes at most three clauses, followed by one output clause. -/
theorem length_tseitin_le {n : ℕ} (c : Circuit .booleanAlgebra n 1) :
    c.tseitin.length ≤ 3 * c.size + 1 := by
  cases c with
  | outputs select => simp [tseitin]
  | gate op args next =>
      have ih := next.length_tseitin_le
      have := CNF.length_ofGate_le op (Fin.val ∘ args) n
      simp only [tseitin, List.length_append, size_gate]
      omega
termination_by c.size

/-- A fixed input makes the output true exactly when it extends to a satisfying assignment. -/
theorem eval_eq_true_iff_tseitin {n : ℕ} (c : Circuit .booleanAlgebra n 1) (x : Fin n → Bool) :
    c.eval x 0 = true ↔
      ∃ a : ℕ → Bool, (∀ i : Fin n, a i.val = x i) ∧ c.tseitin.eval a = true := by
  cases c with
  | outputs select =>
      simp only [eval_outputs, Function.comp_apply, tseitin, CNF.eval_cons, List.any_cons,
        CNF.Literal.eval_pos, List.any_nil, Bool.or_false, CNF.eval_nil, Bool.and_true]
      constructor
      · intro hx
        refine ⟨fun j => if h : j < n then x ⟨j, h⟩ else false, ?_, ?_⟩
        · intro i; simp
        · simpa using hx
      · rintro ⟨a, ha, h⟩
        simpa [ha] using h
  | gate op args next =>
      rw [eval_gate, next.eval_eq_true_iff_tseitin]
      simp only [tseitin, CNF.eval_append, Bool.and_eq_true, CNF.eval_ofGate, beq_iff_eq]
      apply exists_congr
      intro a
      simp only [Fin.forall_fin_succ', Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last,
        Fin.snoc_last, and_assoc]
      exact and_congr_right fun ha => by simp [Function.comp_def, ha]
termination_by c.size

end Circuit

end Complexity
