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

/-- Views `⌜x⌝ₜ = ⌜w⌝ₜ` equating a value's tree code with another value's (such as `Fin`, subtypes,
vectors, or zero-cost rewrites), field equations `g (f a) = v`, and constant-path subtree
equations `⌜e⌝ₜ = ⌜b⌝ₜ.subtree path`. The source translation computes or extracts values through
these equations without changing their codes. -/
register_simp_attr source_view

end Complexity.TreeProgram.Source
