/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.CNF.Basic
public import Complexity.Models.TreeMachine.Language.Derive

/-! # Tree representations and source operations for CNF literals

A literal is encoded as the pair of its variable code and its polarity code.
The existing list encoding then represents clauses and CNFs.
-/

@[expose] public section

namespace Complexity.CNF

attribute [tree_encoding] Literal

/-- The variables of a CNF, listed by occurrence, have a code no larger than the CNF's. -/
theorem size_encode_atoms_le {α : Type*} [UniqueEncoding Tree α] (f : CNF α) :
    ⌜f.atoms⌝ₜ.size ≤ ⌜f⌝ₜ.size := by
  have hc (c : Clause α) : ⌜c.map Literal.atom⌝ₜ.size ≤ ⌜c⌝ₜ.size := by
    induction c with
    | nil => simp
    | cons l c ih =>
      rcases l with ⟨a, b⟩
      simp only [List.map_cons, encode_list_cons, size_encode_prod, Literal.encode_mk] at ih ⊢
      omega
  induction f with
  | nil => simp [atoms]
  | cons c f ih =>
    rw [atoms] at ih ⊢
    have := size_encode_list_append (c.map Literal.atom) (f.flatMap (List.map Literal.atom))
    have := hc c
    simp only [List.flatMap_cons, encode_list_cons, size_encode_prod]
    omega

end Complexity.CNF
