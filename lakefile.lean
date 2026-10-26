import Lake

open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc2"

abbrev complexityOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.unicodeLinter, false⟩, -- Allow multilingual text.
]

abbrev complexityLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    complexityOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package complexity where
  testDriver := "ComplexityTest"
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["Complexity"]
  -- Run the builtin linting steps in addition to the `lintDriver` set above.
  builtinLint := true
  -- A version of Complexity only supports the toolchain it is built with.
  fixedToolchain := true
  -- Allow oleans built on Linux CI to be used across platforms.
  platformIndependent := true
  -- Complexity currently expects artifacts to be in the build directory.
  restoreAllArtifacts := true

@[default_target]
lean_lib Complexity where
  leanOptions := complexityLeanOptions

lean_lib ComplexityTest where
  globs := #[`ComplexityTest.+]
  leanOptions := #[
    ⟨`pp.mvars.anonymous, false⟩, -- Test stability: print `?m.37` as `?_`.
    ⟨`linter.defProp, false⟩] -- Tests name translated programs with `def`.
