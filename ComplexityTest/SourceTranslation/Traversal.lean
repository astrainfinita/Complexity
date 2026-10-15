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

-- Capturing a runtime flag preserves per-element summation.
private def reverseCaptured (input : Bool × List (List Unit)) : List Unit :=
  input.2.foldl (fun _ ys => if input.1 then ys.reverse else ys) []

private def captured : Implementation reverseCaptured := by source_fun_prop

example (m : ℕ) : captured.bounds.time
    (true, List.replicate m () :: [] :: List.replicate m []) = 61 * m + 111 := by
  simp [captured]
  omega

section DependentMap

-- A runtime table and its indices share the same runtime length; the table is captured once.
example : Nonempty (Implementation (fun x : Σ n, (Fin n → ℕ) × List (Fin n) => x.2.2.map x.2.1)) :=
  ⟨by source_fun_prop⟩

-- Pointwise choices must never masquerade as one implementation for all runtime lengths.
example (f : (n : ℕ) → Fin n → Bool) (_hf : ∀ n, Implementation (f n)) : True := by
  fail_if_success
    have : Nonempty (Implementation (fun x : Σ n, List (Fin n) => x.2.map (f x.1))) :=
      ⟨by source_fun_prop⟩
  trivial

end DependentMap

end ComplexityTest.SourceTranslation.Traversal
