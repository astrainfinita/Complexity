/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Implementation
public import Mathlib.Tactic.FunProp

/-! # Registering certified function implementations

The locked `fun_prop` registration helper only accepts `Prop`-valued families. Its
indexing and application interfaces also handle `Implementation`, so register that
family directly and reuse the existing attribute for its definitions.

Certified search must keep an independent `FunProp.State`: its result expressions
inhabit `Implementation`, and its cache must not be passed to `simp` as rewrite proofs.
-/

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  let property ← mkConstWithFreshMVarLevels ``Complexity.TreeProgram.Source.Implementation
  let (args, info, _) ← forallMetaTelescope (← inferType property)
  let some funArgId ← (args.zip info).findIdxM? (fun (arg, binder) => do
      return binder.isExplicit && (← inferType arg).isForall) |
    throwError "certified implementation registration: missing source function"
  let path ← DiscrTree.mkPath (mkAppN property args)
  modifyEnv fun env => funPropDeclsExt.addEntry env
    { funPropName := property.constName!, path, funArgId }
