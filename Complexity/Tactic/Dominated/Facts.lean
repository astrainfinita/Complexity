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
public import Complexity.Encoding.Bool
public import Complexity.Encoding.Tree
public import Complexity.Tactic.Dominated.Attr

/-! # Statements about encodings registered for `dominated`

`dominated` knows encodings only through registrations: the normalization of encoded sizes
(`dominated_simp`, and `dominated_expand` for the pointwise expansion) and the size facts
instantiated at matching terms (`dominated`) and at hypotheses (`dominated_forward`). Lemmas of this
library are registered where they are stated; this file registers those from Lean and Mathlib and
those whose files do not import this one, among them the traversal rules of `Asymptotics`
(`dominated_traversal`). -/

@[expose] public section

namespace Complexity

attribute [dominated_simp] size_encode_prod Sigma.encode_mk size_encode_unit List.length_reverse
  List.length_ofFn FinVector.ofFn_get FinVector.getElem?_toList_val

/- A value of a subtype written with its proof has the code of the value, so the size facts about
the value apply. Only this form is rewritten: `UniqueEncoding.encode_subtype` would also turn the
code of a named value of a subtype into that of its `val`, where the facts about the named value
no longer match; it is used in the pointwise expansion below. -/
attribute [dominated_simp] UniqueEncoding.encode_subtype_mk

attribute [dominated_expand] UniqueEncoding.encode_subtype encode_bool_true encode_bool_false
  List.length_cons List.length_nil List.length_append List.length_map
  encode_option_some encode_option_none Fin.val_last

/- A tree is its own code, so a source building trees leaves `Tree.nil` and `Tree.pair` in a
growth; their sizes are the defining equations of `Tree.size`. -/
attribute [dominated_expand] Tree.encode_self Tree.size_nil Tree.size_pair

attribute [dominated] Tree.size_pos size_encode_bool_le Fin.isLt size_encode_finVector_fin_le

/- The traversal rules of `Asymptotics`. For each kind they are tried in this order: a maximum over
a list of the elements that occur before a maximum over a list of dependent elements, then a sum
over `List.finRange`, then a sum over a list of the elements that occur. -/
attribute [dominated_traversal] Dominated.list_foldr_max_le Dominated.foldr_max_le
  IsPoly.list_foldr_max IsPoly.foldr_max IsPoly.sum_finRange IsPoly.list_sum
attribute [dominated_traversal mul] Dominated.sum_finRange_of_mul Dominated.list_sum_of_mul

end Complexity
