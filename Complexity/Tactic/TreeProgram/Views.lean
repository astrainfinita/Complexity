/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.TreeSize
public import Complexity.Encoding.Option
public import Complexity.Encoding.Sigma
public import Complexity.Encoding.Fin
public import Complexity.Encoding.Vector
public import Complexity.Encoding.Bool
public import Complexity.Encoding.Tree
public import Complexity.Tactic.TreeProgram.Attributes

/-! # Views registered for the source translation

The source translation computes a value of a type stored as a field through that field
(`source_view`). Views and field equations of this library are registered where they are stated;
this file registers those from Lean and Mathlib and those whose files do not import the tactic
layer. Raw trees, whose identity encoding is stated with the encodings, are also matched on here,
by their constructors `nil` and `pair` (`Tree.caseView`). -/

@[expose] public section

namespace Complexity

attribute [source_view] Fin.val_castSucc Fin.val_castAdd Fin.val_natAdd Fin.val_succ Fin.val_last
  Fin.val_zero Vector.toList_push Vector.toList_append encode_ofFn encode_fin_function_codes
  Tree.encode_encode Tree.encode_pair Tree.encode_spine

-- The views have a variable on the left; the more specific equations come first.
attribute [source_view low] encode_fin UniqueEncoding.encode_subtype encode_fin_function_vector
  encode_vector UniqueEncoding.encode_eqRec

open TreeProgram in
/-- Raw trees, with the identity encoding, as the constructors `nil` and `pair`. -/
instance Tree.caseView : CaseView Tree 2 where
  Payload i := match i with | 0 => PUnit | 1 => Tree × Tree
  encoding i := match i with
    | 0 => inferInstanceAs (UniqueEncoding Tree PUnit)
    | 1 => inferInstanceAs (UniqueEncoding Tree (Tree × Tree))
  ofPayload i p := match i, p with | 0, _ => .nil | 1, (a, b) => .pair a b
  exists_ofPayload t := match t with | .nil => ⟨0, PUnit.unit, rfl⟩ | .pair a b => ⟨1, (a, b), rfl⟩
  elim t g := match (generalizing := false) h : t with
    | .nil => g 0 PUnit.unit h
    | .pair a b => g 1 (a, b) h
  elim_ofPayload i p _ := match i, p with | 0, _ => rfl | 1, (_, _) => rfl
  dispatch := .test [] (.leaf 1 []) (.leaf 0 [])
  select_encode i p := match i, p with | 0, _ => rfl | 1, (_, _) => rfl

end Complexity
