/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Encoding.TreeSize
public import Complexity.Encoding.Option
public import Complexity.Tactic.TreeProgram.Attributes

/-! # Statements about encodings used by the automation

`dominated` and the source translation know encodings only through registrations: the
normalization of encoded sizes (`dominated_simp`, and `dominated_expand` for the pointwise
expansion), the size facts instantiated at matching terms (`dominated`) and at hypotheses
(`dominated_forward`), and the types stored as a field with the field's operations
(`source_view`). Lemmas of this library are
registered where they are stated; this file registers those from Lean and Mathlib and those whose
files do not import the tactic layer. -/

@[expose] public section

namespace Complexity

attribute [dominated_simp] size_encode_prod Sigma.encode_mk size_encode_unit List.length_reverse
  encode_fin_function_codes encode_vector_ofFn Vector.toList_ofFn Vector.length_toList
  List.length_ofFn size_encode_ofFn

attribute [dominated_expand] UniqueEncoding.encode_subtype encode_bool_true encode_bool_false
  List.length_cons List.length_nil List.length_append List.length_map
  encode_option_some encode_option_none Fin.val_last

/- A tree is its own code, so a source building trees leaves `Tree.nil` and `Tree.pair` in a
growth; their sizes are the defining equations of `Tree.size`. -/
attribute [dominated_expand] Tree.encode_self Tree.size_nil Tree.size_pair

attribute [source_view] Fin.val_castSucc Fin.val_castAdd Fin.val_natAdd Fin.val_succ Fin.val_last
  Fin.val_zero Vector.toList_push Vector.toList_append encode_ofFn encode_fin_function_codes
  Tree.encode_encode

-- The views have a variable on the left; the more specific equations come first.
attribute [source_view low] encode_fin UniqueEncoding.encode_subtype encode_fin_function_vector
  encode_vector

attribute [dominated] Tree.size_pos size_encode_bool_le Fin.isLt size_encode_fin_table_le

end Complexity
