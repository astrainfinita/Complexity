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

attribute [fun_prop] Complexity.TreeProgram.Source.HasProgram

public meta section

namespace Complexity.TreeProgram.Source

open Lean Meta

/-- The program of an implementation, with the programs of the implementations it is built from
unfolded down to code. -/
def unfoldPrograms (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOf ``Implementation.program && e.getAppNumArgs ≥ 8 then
      let x ← whnf (e.getArg! 7)
      if x.isAppOf ``Implementation.mk then
        return .visit (mkAppN (x.getArg! (x.getAppNumArgs - 2))
          (e.getAppArgs.extract 8 e.getAppNumArgs)).headBeta
    return .continue)

/-- On an implementation `N.implementationS` whose program does not depend on the parameters (such
as the types of a polymorphic function), add that program, unfolded, as `N.programS`, and
`N.hasProgram_s : HasProgram f N.programS time peak` at every value of the parameters, registered
for uses at types that depend on the input. For other names, `uniform_program N.s` gives the stem,
in the current namespace (as `mk_iff` takes a name). Names follow `Nat.decidablePrime`. -/
syntax (name := uniformProgram) "uniform_program" (ppSpace ident)? : attr

open Mathlib.Meta.FunProp in
initialize registerBuiltinAttribute {
  name := `uniformProgram
  descr := "name the program of an implementation, which does not depend on its parameters"
  applicationTime := .afterCompilation
  add := fun impl stx kind => MetaM.run' do
    let stem ← match stx with
      | `(attr| uniform_program $name:ident) =>
        pure (← Elab.mkDeclName (← getCurrNamespace) {} name.getId).1
      | _ =>
        let some s := (impl.getString!.dropPrefix? "implementation").map (·.toString) |
          throwError "uniform_program: name {.ofConstName impl} `N.implementationS`, or give the \
            stem with `uniform_program N.s`"
        unless s.front.isUpper do
          throwError "uniform_program: name {.ofConstName impl} `N.implementationS`, or give the \
            stem with `uniform_program N.s`"
        pure (impl.getPrefix ++ Name.mkSimple s.decapitalize)
    let info ← getConstInfo impl
    let fact ← forallTelescope info.type fun xs type => do
      unless type.isAppOfArity ``Implementation 7 do
        throwError "uniform_program: {.ofConstName impl} is not an implementation"
      let args := type.getAppArgs
      let implementation := mkAppN (mkConst impl (info.levelParams.map mkLevelParam)) xs
      let program ← instantiateMVars
        (← unfoldPrograms (← mkAppM ``Implementation.program #[implementation]))
      let used := xs.filter (program.containsFVar ·.fvarId!)
      unless used.isEmpty do
        throwError "uniform_program: the program of {.ofConstName impl} depends on {used.toList}"
      let programName := stem.getPrefix ++ Name.mkSimple ("program" ++ stem.getString!.capitalize)
      let programLevels := (collectLevelParams {} program).params.toList
      addAndCompile <| .defnDecl {
        name := programName, levelParams := programLevels
        type := ← mkArrow (mkConst ``Value) (mkApp (mkConst ``Code) (mkConst ``Value))
        value := program, hints := .regular (getMaxHeight (← getEnv) program + 1)
        safety := .safe }
      addDocStringCore programName s!"The program of `{impl}` (`uniform_program`)."
      let fact := stem.getPrefix ++ Name.mkSimple ("hasProgram_" ++ stem.getString!)
      let statement ← mkAppM ``HasProgram #[args[4]!,
        mkConst programName (programLevels.map mkLevelParam), args[5]!, args[6]!]
      -- The kernel identifies the named program with the implementation's.
      addDecl <| .thmDecl {
        name := fact, levelParams := info.levelParams, type := ← mkForallFVars xs statement
        value := ← mkLambdaFVars xs
          (← mkAppM ``HasProgram.mk #[← mkAppM ``Implementation.sound #[implementation]]) }
      addDocStringCore fact s!"`{impl}` with its program at every type (`uniform_program`)."
      return fact
    addTheorem fact kind
}

end Complexity.TreeProgram.Source
