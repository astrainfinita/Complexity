/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import ComplexityTest.TreeRun

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Traversal

private def mapInput : List (List Bool) := [[true, false], [], [false, true, true]]
private def mapOutput : List (List Bool) := [[false, true], [], [true, true, false]]

-- The joint Writer evaluation computes both the source result and the sum budget.
#guard ((Implementation.reverse (α := Bool)).map.evaluate mapInput).value == mapOutput
#guard ((Implementation.reverse (α := Bool)).map.evaluate mapInput).cost.time == 182

-- The same certificate stores executable model code, not an opaque existential witness.
private def mapReverseCode := (Implementation.reverse (α := Bool)).map.program .input
#guard let p := mapReverseCode
  let c := ComplexityTest.TreeRun.runFrom p.compile
    (p.compile.initInput (Config := TreeMachine.Cfg p.registers _) ⌜mapInput⌝ₜ) 186
  p.compile.halt c.state && decide (c.regs 0 = ⌜mapOutput⌝ₜ)

-- One long callback and many empty callbacks have linear, not quadratic, total time.
private def foldedReverse : Implementation
    (fun x : List Unit × List (List Unit) => x.2.foldl (fun _ ys => ys.reverse) x.1) := by
  source_fun_prop

example (m : ℕ) : foldedReverse.bounds.time
    ([], List.replicate m () :: [] :: List.replicate m []) = 35 * m + 54 := by
  simp [foldedReverse]
  omega

example (a : List Unit) (xs : List (List Unit)) :
    foldedReverse.bounds.peak (a, xs) ≤ ⌜(a, xs)⌝ₜ.size := by
  simp [foldedReverse]
  refine (foldlCost_peak_le _ _ ?_ ?_).trans ?_
  · intros; simp
  · intros; simp
  · omega

-- The coarse estimate changes only the certificate, keeping the implementing program.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : β → α → β}
    (hf : Implementation (Function.uncurry f)) : hf.foldlUniform.program = hf.foldl.program := rfl

-- Capturing a runtime flag preserves per-element summation.
private def reverseCaptured (input : Bool × List (List Unit)) : List Unit :=
  input.2.foldl (fun _ ys => if input.1 then ys.reverse else ys) []

private def captured : Implementation reverseCaptured := by source_fun_prop

example (m : ℕ) : captured.bounds.time
    (true, List.replicate m () :: [] :: List.replicate m []) = 61 * m + 111 := by
  simp [captured]
  omega

section DependentMap

attribute [local fun_prop] Realizes.comp Realizes.of_encode Realizes.pair
  fst_realizes snd_realizes identity_realizes encode_realizes finApply_realizes
  Realizes.mapDependentWith

-- A runtime table and its indices share the same runtime length; the table is captured once.
example : ∃ b, Realizes
    (fun x : Σ n, (Fin n → ℕ) × List (Fin n) => x.2.2.map x.2.1) b :=
  ⟨_, by source_fun_prop⟩

-- Pointwise choices must never masquerade as one implementation for all runtime lengths.
example (f : (n : ℕ) → Fin n → Bool) (b : (n : ℕ) → Bounds (Fin n))
    (_hf : ∀ n, Realizes (f n) (b n)) : True := by
  fail_if_success
    have : ∃ c, Realizes (fun x : Σ n, List (Fin n) => x.2.map (f x.1)) c :=
      ⟨_, by source_fun_prop⟩
  trivial

end DependentMap

end ComplexityTest.SourceTranslation.Traversal
