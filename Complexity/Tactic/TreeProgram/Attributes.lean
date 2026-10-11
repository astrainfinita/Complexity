/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.Meta.Tactic.Simp.Attr
public meta import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp.RegisterCommand

public meta section

/-- Project certified budgets before simplifying their source functions. -/
register_simp_attr source_bounds

namespace Complexity.TreeProgram.Source

/-- Function rules tried after structural field extraction; priority only orders rules
within the same stage. This label does not register a `fun_prop` theorem. -/
initialize sourceFallbackAttr : Lean.LabelExtension ←
  Lean.registerLabelAttr `source_fallback
    "try this source function rule after structural field extraction"

end Complexity.TreeProgram.Source
