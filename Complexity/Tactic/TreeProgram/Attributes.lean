/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Attr

public meta section

namespace Complexity.TreeProgram.Source

/-- Function rules tried after structural field extraction; priority only orders rules
within the same stage. This label does not register a `fun_prop` theorem. -/
initialize sourceFallbackAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `source_fallback
    "try this source function rule after structural field extraction"

/-- Explicit source choices take precedence over default lambda implementations.
Mathlib's lambda-rule registry does not retain theorem priorities. -/
initialize sourceSavedImplementationExt : Lean.LabelExtension ← Lean.mkLabelExt

/-- Statements `a ≤ b`, `a < b` or `a = b` about a term, such as the size of an encoding, that
`dominated` instantiates at every matching term when comparing pointwise. The term is the left
side, without an added literal, or the right side when the left side is a variable or a literal;
the terms of the other side are looked at in the next round. -/
initialize dominatedAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `dominated
    "instantiate this statement at matching terms when `dominated` compares pointwise"

/-- Statements `p → a ≤ b` (or `<`, `=`), such as a bound on a list element's size, that
`dominated` instantiates at every local hypothesis matching their first explicit premise `p` when
comparing pointwise, as forward reasoning in the manner of `@[gcongr_forward]`. The terms of an
instance are not looked at in a next round. -/
initialize dominatedForwardAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `dominated_forward
    "instantiate this statement at each matching hypothesis when `dominated` compares pointwise"

/-- Equations normalizing encoded sizes, used by `dominated` on the left side before splitting
it and in the pointwise step. -/
register_simp_attr dominated_simp

/-- Equations expanding encoded sizes, used by `dominated` only in the pointwise step, after the
input is destructured and its cases are split. -/
register_simp_attr dominated_expand

/-- Encoding equations used when deciding finite source cases. -/
register_simp_attr source_case_simp

end Complexity.TreeProgram.Source
