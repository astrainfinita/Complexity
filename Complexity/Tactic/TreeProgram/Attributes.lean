/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Attr
public import Complexity.Tactic.Dominated.Attr

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

/-- Views `⌜x⌝ₜ = ⌜x.1⌝ₜ` of a structure stored as its data field, such as `Fin` and subtypes, and
equations `(f a).1 = v` for the field of an operation. The source translation computes a value of
such a type as its field. -/
register_simp_attr source_view

end Complexity.TreeProgram.Source
