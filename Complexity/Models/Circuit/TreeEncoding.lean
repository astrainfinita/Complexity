/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic
public import Complexity.Models.TreeMachine.Language.Derive
public import Complexity.Encoding.Nat
public import Complexity.Encoding.Fin
public import Complexity.Encoding.Sigma

/-! # Tree encodings and source operations for circuits

Input and output counts are supplied by the circuit type. A gate stores its arity,
operation symbol, input wires, and continuation, in that order.
-/

@[expose] public section

namespace Complexity

attribute [tree_encoding] Circuit

namespace Circuit

theorem size_le_size_encode {L : FirstOrder.Language}
    [∀ k, UniqueEncoding Tree (L.Functions k)] {n m : ℕ} (c : Circuit L n m) :
    c.size ≤ ⌜c⌝ₜ.size := by
  induction c with
  | outputs _ => exact Nat.zero_le _
  | gate op args next ih =>
    simp only [size_gate, encode_gate, size_encode_prod, size_encode_unit]
    omega

theorem outputs_le_size_encode {L : FirstOrder.Language}
    [∀ k, UniqueEncoding Tree (L.Functions k)] {n m : ℕ} (c : Circuit L n m) :
    m ≤ ⌜c⌝ₜ.size := by
  induction c with
  | outputs select =>
    have := card_le_size_encode_fin_function select
    simp only [encode_outputs, size_encode_prod, size_encode_unit]
    omega
  | gate op args next ih =>
    simp only [encode_gate, size_encode_prod, size_encode_unit]
    omega

end Circuit

end Complexity
