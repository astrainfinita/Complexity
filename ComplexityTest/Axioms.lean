/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity
meta import Lean.Elab.Command

/-! # The library depends only on the standard axioms

Guards that every declaration of the library that an importing module sees depends on no axiom
other than `propext`, `Classical.choice` and `Quot.sound`. A `sorry` already fails the build; this
check also rejects a declared `axiom` and the axioms that `native_decide` brings in. The other
tests therefore do not repeat it for single theorems with `#print axioms`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array MessageData := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`Complexity).isPrefixOf env.header.moduleNames[i] do continue
    for n in env.header.moduleData[i]!.constNames do
      for a in ← liftCoreM (collectAxioms n) do
        unless allowed.contains a do
          bad := bad.push (if a == n then m!"{n} is an axiom" else m!"{n} depends on {a}")
  unless bad.isEmpty do
    throwError "declarations depending on other axioms:{indentD (.joinSep bad.toList "\n")}"
