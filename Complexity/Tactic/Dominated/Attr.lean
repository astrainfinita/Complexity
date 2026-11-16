/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Attr

/-! # Registrations for `dominated`

The facts `dominated` knows about a library: statements instantiated at matching terms or
hypotheses, the rules comparing a traversal entry by entry, and the simp sets normalizing and
expanding encoded sizes. Lemmas are registered where they are stated. -/

public meta section

namespace Complexity.Tactic.Dominated

/-- Statements `a ≤ b`, `a < b` or `a = b` about a term, such as the size of an encoding, that
`dominated` instantiates at every matching term when comparing pointwise. The term is the left
side, without an added literal, or the right side when the left side is a variable or a literal;
the terms of the other side are looked at in the next round. Statements `IsPoly r T`, possibly
with premises determined by `T`, are used on `IsPoly` goals at the parts `T a` they match; each
kind is indexed by its own shape. -/
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

/-- A rule registered with `@[dominated_traversal]`. Whether it proves `Dominated` or `IsPoly` is
read from its conclusion when it is registered. -/
structure TraversalRule where
  /-- The rule. -/
  name : Lean.Name
  /-- Whether its premises are normalized distributing a table length over an entry. -/
  mul : Bool
  /-- Whether it concludes `IsPoly`, rather than `Dominated`. -/
  poly : Bool
  deriving Inhabited

/-- The rules registered with `@[dominated_traversal]`, in the order of registration. -/
initialize dominatedTraversalExt :
    Lean.SimpleScopedEnvExtension TraversalRule (Array TraversalRule) ←
  Lean.registerSimpleScopedEnvExtension { addEntry := Array.push, initial := #[] }

/-- Statements proving a growth comparison over a traversal entry by entry, such as a maximum over a
list or a sum over a table: a conclusion `Dominated f g` or `IsPoly s f` whose premises are again
such comparisons, on the domain of the elements. `dominated` applies the rules of a goal's kind to
each of its summands, in the order of registration, and splits each premise after expanding
encoded sizes; with `mul` it also distributes a table length over an entry. -/
syntax (name := dominatedTraversal) "dominated_traversal" (&" mul")? : attr

initialize Lean.registerBuiltinAttribute {
  name := `dominatedTraversal
  descr := "apply this rule to the summands of a growth comparison of its kind in `dominated`"
  applicationTime := .afterCompilation
  add := fun name stx kind => Lean.Meta.MetaM.run' do
    let poly ← Lean.Meta.forallTelescopeReducing (← Lean.getConstInfo name).type fun _ type => do
      if type.isAppOfArity `Complexity.IsPoly 3 then return true
      if type.isAppOf `Complexity.Dominated then return false
      Lean.throwError "`dominated_traversal` expects a statement concluding `Dominated` or `IsPoly`"
    dominatedTraversalExt.add { name, mul := !stx[1].isNone, poly } kind }

/-- Equations normalizing encoded sizes, used by `dominated` on the left side before splitting
it and in the pointwise step. -/
register_simp_attr dominated_simp

/-- Equations expanding encoded sizes, used by `dominated` only in the pointwise step, after the
input is destructured and its cases are split. -/
register_simp_attr dominated_expand

end Complexity.Tactic.Dominated
