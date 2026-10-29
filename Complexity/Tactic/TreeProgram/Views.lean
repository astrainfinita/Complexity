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
layer. -/

@[expose] public section

namespace Complexity

attribute [source_view] Fin.val_castSucc Fin.val_castAdd Fin.val_natAdd Fin.val_succ Fin.val_last
  Fin.val_zero Vector.toList_push Vector.toList_append encode_ofFn encode_fin_function_codes
  Tree.encode_encode

-- The views have a variable on the left; the more specific equations come first.
attribute [source_view low] encode_fin UniqueEncoding.encode_subtype encode_fin_function_vector
  encode_vector UniqueEncoding.encode_eqRec

end Complexity
