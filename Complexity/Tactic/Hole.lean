/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.DeclModifiers
public meta import Lean.Meta.Closure
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Util.CollectFVars
import Mathlib.Tactic.Linter.UnusedTacticExtension

/-! # Holes in statements

`hole(x, y ⊢ a)` is a part `a` of a statement left to be filled in its proof. It may depend on the
listed variables `x, y` of the statement and on nothing else: they are its context, which stays
the statement's whatever the proof does to the goal. Only `fill_hole` fills a hole; unification
does not, unlike `?a`, and `?a` written in a term is a new metavariable.

* `fill_hole a := e` fills the hole `a` with `e`, written in the hole's context.
* `fill_hole a in tac` runs `tac` with the hole `a` open to unification; `tac` must fill it.
* `abstract_hole a using N` makes the value of the hole `a` a definition `N`, taking the hole's
  context variables, which stands for the hole in the statement. `N` is named next to the
  declaration whose statement has the hole. The hole may be filled later.

In goals a hole shows its context as written, with `x := t` where the goal replaced `x` by `t`.

A hole is a metavariable over its context variables, applied to them, recorded in `infoExt`. It
lives at a depth no unification runs at, `holeDepth`, has an inaccessible name, and counts as older
than any term of a proof, so that no tactic takes it for a new goal.
-/

public meta section

open Lean Meta Elab Term Tactic PrettyPrinter Delaborator SubExpr

namespace Complexity.Hole

/-- A variable of a hole's context; `x := t` appears only in goals, where the goal replaced `x`
by `t`. -/
syntax holeVar := ident (" := " term)?

/-- `hole(x, y ⊢ a)` is a part `a` of a statement, depending on its variables `x, y`, left to be
filled by `fill_hole` in the proof. -/
syntax (name := hole) "hole(" (holeVar,+ ppSpace)? "⊢ " ident ")" : term

/-- The depth of holes: no unification runs at it, so only `fill_hole` fills them. -/
def holeDepth : Nat := 1000000

/-- What is settled about a hole besides its metavariable: whether its statement is exported, and
the definition `abstract_hole` named for its value, with the name as written. -/
structure Info where
  /-- Whether the statement with the hole is exported. -/
  exported : Bool
  /-- The definition the value of the hole becomes, and its name as written. -/
  definition? : Option (Name × Syntax) := none

/-- The holes made by `hole(…)`. -/
initialize infoExt : EnvExtension (MVarIdMap Info) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- Closes a hole to unification. -/
def close (m : MVarId) : MetaM Unit :=
  modifyMCtx (·.modifyExprMVarDecl m ({ · with depth := holeDepth, kind := .syntheticOpaque }))

/-- The hole named `a` of the declaration being elaborated, if any. -/
def find? (a : Name) : MetaM (Option (MVarId × Info)) := do
  for (m, info) in infoExt.getState (← getEnv) do
    if let some d := (← getMCtx).findDecl? m then
      if d.userName.eraseMacroScopes == a then return some (m, info)
  return none

@[term_elab hole, inherit_doc hole]
def elabHole : TermElab := fun stx expectedType? => do
  let `(hole($[$vars,*]? ⊢ $a)) := stx | throwUnsupportedSyntax
  let mut xs := #[]
  for var in (vars.map (·.getElems)).getD #[] do
    let `(holeVar| $x:ident) := var |
      throwErrorAt var "a hole lists variables; `x := t` appears only in goals"
    let some d := (← getLCtx).findFromUserName? x.getId | throwErrorAt x "unknown variable `{x}`"
    if xs.contains d.toExpr then throwErrorAt x "`{x}` is listed twice"
    if d.isLet then throwErrorAt x "`{x}` is a `let` variable"
    for y in (collectFVars {} (← instantiateMVars d.type)).fvarIds do
      unless xs.contains (.fvar y) do
        throwErrorAt x "the type of `{x}` mentions `{Expr.fvar y}`, which must be listed before it"
    xs := xs.push d.toExpr
  let type ← tryPostponeIfHasMVars expectedType? s!"the type of the hole `{a.getId}` is not known"
  for y in (collectFVars {} type).fvarIds do
    unless xs.contains (.fvar y) do
      throwError "the type of the hole `{a}` mentions `{Expr.fvar y}`, which it does not list"
  if (← find? a.getId).isSome then throwError "there is already a hole `{a}`"
  let hole ← mkFreshExprMVarAt {} {} (← mkForallFVars xs type) .syntheticOpaque
    (← mkFreshUserName a.getId) xs.size
  -- Older than the terms of any proof, it is never a new goal of a tactic.
  modifyMCtx (·.modifyExprMVarDecl hole.mvarId! ({ · with index := 0 }))
  close hole.mvarId!
  let info := { exported := (← getEnv).isExporting }
  modifyEnv (infoExt.modifyState · (·.insert hole.mvarId! info))
  return mkAppN hole xs

/-- The hole `a`, for a tactic about it. Lean checks a statement for unfilled parts before its
proof, so a hole is reported unfilled only once a tactic is about it. -/
def get (a : Ident) : TermElabM (MVarId × Info) := do
  let some (m, info) ← find? a.getId | throwErrorAt a "there is no hole `{a}`"
  registerMVarErrorCustomInfo m a m!"the hole `{a}` is not filled"
  return (m, info)

/-- The hole `a`, for a tactic filling it. -/
def getOpen (a : Ident) : TermElabM (MVarId × Info) := do
  let (m, info) ← get a
  if ← m.isAssigned then throwErrorAt a "the hole `{a}` is already filled"
  return (m, info)

/-- Fills the hole `a` with `v`, a value over its context, or with the definition named for it. -/
def assign (a : Ident) (m : MVarId) (info : Info) (v : Expr) : TermElabM Unit := do
  let v ← instantiateMVars v
  if v.hasExprMVar then throwErrorAt a "the hole `{a}` is only partly filled:{indentExpr v}"
  let some (n, ref) := info.definition? | m.assign v
  withExporting (isExporting := info.exported) do
    m.assign (← mkAuxDefinition n (← m.getType) v)
  addDeclarationRangesFromSyntax n ref
  if let some decl ← getDeclName? then
    addDocStringCore n s!"The value of the hole `{a.getId}` of `{decl}`."

/-- `fill_hole a := e` fills the hole `a` with `e`, written in the hole's context.
`fill_hole a in tac` runs `tac` with the hole `a` open to unification; `tac` must fill it. -/
elab (name := fillHole) "fill_hole " a:ident " := " e:term : tactic => do
  let (m, info) ← getOpen a
  let decl ← m.getDecl
  let v ← withLCtx {} {} <| forallBoundedTelescope decl.type decl.numScopeArgs fun xs type => do
    try
      mkLambdaFVars xs (← Term.withoutErrToSorry <| Term.withSynthesize <|
        Term.elabTermEnsuringType e type)
    catch ex =>
      unless ex.toMessageData.hasTag (· == unknownIdentifierMessageTag) do throw ex
      let context := if xs.isEmpty then m!"has no variables" else
        m!"consists of {MessageData.andList (xs.toList.map (m!"`{·}`"))}"
      throwErrorAt ex.getRef "{ex.toMessageData}\n\n\
        The value is written in the context of the hole `{a}`, which {context}."
  assign a m info v

@[tactic_alt fillHole]
elab (name := fillHoleIn) "fill_hole " a:ident " in " tac:tacticSeq : tactic => do
  let (m, info) ← getOpen a
  let depth := (← getMCtx).depth
  modifyMCtx (·.modifyExprMVarDecl m ({ · with depth, kind := .natural }))
  try evalTactic tac finally close m
  unless ← m.isAssigned do throwErrorAt a "the tactic did not fill the hole `{a}`"
  assign a m info (.mvar m)

/-- `abstract_hole a using N` makes the value of the hole `a` a definition `N`, taking the hole's
context variables, which stands for the hole in the statement. `N` is named next to the
declaration whose statement has the hole. The hole may be filled later. -/
elab (name := abstractHole) "abstract_hole " a:ident " using " n:ident : tactic => do
  let (m, info) ← get a
  if info.definition?.isSome then throwErrorAt a "the hole `{a}` is already abstracted"
  -- Next to the declaration whose statement has the hole, public or private like the statement.
  let space ← match ← getDeclName? with
    | some decl => pure (privateToUserName decl).getPrefix
    | none => getCurrNamespace
  let (name, _) ← withExporting (isExporting := info.exported) do
    mkDeclName space {} n.getId
  let info := { info with definition? := some (name, n) }
  modifyEnv (infoExt.modifyState · (·.insert m info))
  if ← m.isAssigned then assign a m info (.mvar m)

@[delab app, delab mvar, inherit_doc hole]
def delabHole : Delab := do
  let .mvar m := (← getExpr).getAppFn | failure
  guard ((infoExt.getState (← getEnv)).contains m)
  let decl ← m.getDecl
  let names := decl.type.getForallBinderNames.take decl.numScopeArgs
  withOverApp decl.numScopeArgs do
    let args := (← getExpr).getAppArgs
    let vars ← (names.toArray.zip args).mapIdxM fun i (x, t) => do
      -- The variable itself, as the statement wrote it, or what the goal replaced it by.
      if t.isFVar && ((← getLCtx).find? t.fvarId!).any (·.userName == x) then
        `(holeVar| $(mkIdent x):ident)
      else
        `(holeVar| $(mkIdent x):ident := $(← withNaryArg i delab))
    let a := mkIdent decl.userName.eraseMacroScopes
    if vars.isEmpty then `(hole(⊢ $a)) else `(hole($vars,* ⊢ $a))

-- They fill and name holes, which are not goals.
#allow_unused_tactic! fillHole abstractHole

end Complexity.Hole
