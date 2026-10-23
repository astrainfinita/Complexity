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

`dominated` and finite source cases know encodings only through registrations: the normalization
of encoded sizes (`dominated_simp`, and `dominated_expand` for the pointwise expansion), the size
facts instantiated at matching terms (`dominated`) and at hypotheses (`dominated_forward`), and the
encoding equations of finite source cases (`source_case_simp`). Lemmas of this library are
registered where they are stated; this file registers those from Lean and Mathlib and those whose
files do not import the tactic layer. -/

@[expose] public section

namespace Complexity

attribute [dominated_simp] size_encode_prod Sigma.encode_mk size_encode_unit List.length_reverse

attribute [dominated_expand] UniqueEncoding.encode_subtype encode_bool_true encode_bool_false
  List.length_cons List.length_nil List.length_append List.length_map
  encode_option_some encode_option_none Fin.val_last

/- A tree is its own code, so a source building trees leaves `Tree.nil` and `Tree.pair` in a
growth; their sizes are the defining equations of `Tree.size`. -/
attribute [dominated_expand] Tree.encode_self Tree.size_nil Tree.size_pair

attribute [source_case_simp] encode_unit encode_prod List.ofFn_succ

attribute [dominated] Tree.size_pos size_encode_bool_le Fin.isLt size_encode_fin_table_le

end Complexity
