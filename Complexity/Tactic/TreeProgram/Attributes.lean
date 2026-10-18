/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.LabelAttribute

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

/-- Statements `a ≤ b` or `a = b` about specific functions, such as the size of an encoding, that
`dominated` instantiates at every matching term when comparing pointwise. -/
initialize dominatedAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `dominated
    "instantiate this statement at matching terms when `dominated` compares pointwise"

end Complexity.TreeProgram.Source
