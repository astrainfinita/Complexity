/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Tseitin
public import Complexity.Models.Circuit.TreeEncoding
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding
public import Complexity.Data.CNF.TreeEncoding

/-! # Encoded size of Tseitin formulas

The input includes the binary input count. Unused inputs and sparse wire indices are allowed;
the bound uses the encoded description size, not the number of available wires.
-/

@[expose] public section

namespace Complexity.CNF

/-- A gate's output-size estimate depends only on its ordinary clause definition. -/
theorem size_encode_ofGate_le {α : Type*} [UniqueEncoding Tree α] {k : ℕ}
    (op : FirstOrder.Language.booleanAlgebra.Functions k) (args : Fin k → α) (out : α) :
    ⌜CNF.ofGate op args out⌝ₜ.size ≤ 4 * ⌜(⟨k, op, args, out⟩ :
      Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → α) × α)⌝ₜ.size := by
  change _ ≤ 4 * (1 + ⌜k⌝ₜ.size + (1 + ⌜op⌝ₜ.size + (1 + ⌜args⌝ₜ.size + ⌜out⌝ₜ.size)))
  cases op <;> simp [CNF.ofGate, List.ofFn_succ] <;> omega

end Complexity.CNF

namespace Complexity.Circuit

open FirstOrder

/-- The Tseitin formula has quadratic encoded size in the complete circuit input.
The pair `(n, c)` has the same encoding as the dependent pair used by `CircuitSAT`. -/
@[dominated] theorem size_encode_tseitin_le {n : ℕ} (c : Circuit .booleanAlgebra n 1) :
    ⌜c.tseitin⌝ₜ.size ≤ 8 * ⌜(n, c)⌝ₜ.size ^ 2 := by
  cases c with
  | outputs select =>
      have h := Nat.le_self_pow (by decide : 2 ≠ 0)
        ⌜(n, (outputs select : Circuit .booleanAlgebra n 1))⌝ₜ.size
      simp [List.ofFn_succ] at *
      omega
  | gate op args next =>
      have hn := size_encode_nat_succ_le n
      have hb : ⌜(n + 1, next)⌝ₜ.size + 1 ≤ ⌜(n, gate op args next)⌝ₜ.size := by
        simp only [encode_gate, size_encode_prod, size_encode_unit]
        omega
      have hg : ⌜CNF.ofGate op (Fin.val ∘ args) n⌝ₜ.size ≤
          4 * ⌜(n, gate op args next)⌝ₜ.size := by
        have h := CNF.size_encode_ofGate_le op (Fin.val ∘ args) n
        have hv : ⌜Fin.val ∘ args⌝ₜ.size = ⌜args⌝ₜ.size :=
          congrArg Tree.size (encode_fin_values args)
        simp only [Sigma.encode_mk, encode_gate, size_encode_prod, size_encode_unit, hv] at h ⊢
        omega
      have hi := next.size_encode_tseitin_le
      have ha := size_encode_list_append (CNF.ofGate op (Fin.val ∘ args) n) next.tseitin
      simp only [tseitin]
      nlinarith
termination_by c.size

end Complexity.Circuit
