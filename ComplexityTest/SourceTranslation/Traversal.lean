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

-- The program of a certificate is executable model code.
private def mapReverseCode := List.Code.map List.Code.reverse .input
#guard let p := mapReverseCode
  let c := ComplexityTest.TreeRun.runFrom p.compile
    (p.compile.init ⌜mapInput⌝ₜ) 186
  p.compile.halt c.1 && decide (c.2.regs 0 = ⌜mapOutput⌝ₜ)

-- One long callback and many empty callbacks have linear, not quadratic, total time.
example : HasProgram
    (fun x : List Unit × List (List Unit) => x.2.foldl (fun _ ys => ys.reverse) x.1)
    hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop
  · apply Dominated.of_le_mul 2
    rintro ⟨a, xs⟩
    have ht := foldlTime_le_sum (f := fun _ ys : List Unit => ys.reverse)
      (fun ys => 1 + ⌜ys⌝ₜ.size) (fun _ => le_rfl) a xs
    have hs := size_encode_list xs
    simp [List.sum_map_add] at ht ⊢
    omega
  · apply Dominated.of_le
    rintro ⟨a, xs⟩
    have := foldlPeak_le_of_size (f := fun _ ys : List Unit => ys.reverse)
      (p := fun z => max ⌜z⌝ₜ.size ⌜z.2⌝ₜ.size) a xs (fun _ _ => by simp [size_encode_prod])
      (fun _ _ => by simp [size_encode_prod])
    simp [size_encode_prod]
    omega

-- Capturing a runtime flag preserves per-element summation.
private def reverseCaptured (input : Bool × List (List Unit)) : List Unit :=
  input.2.foldl (fun _ ys => if input.1 then ys.reverse else ys) []

example := (by
    source_fun_prop
    apply Dominated.of_le_mul 6
    rintro ⟨b, xs⟩
    have := foldlTime_le_sum (f := fun _ ys : List Unit => if b then ys.reverse else ys)
      (t := fun z => 1 + (if b = true then 1 + ⌜z.2⌝ₜ.size else 1) + 1)
      (fun ys => 5 + ⌜ys⌝ₜ.size) (fun _ => by split <;> omega) [] xs
    have hs := size_encode_list xs
    simp [List.sum_map_add] at this ⊢
    omega : HasProgram reverseCaptured _ (fun x => ⌜x⌝ₜ.size) _)

section DependentMap

-- A runtime table and its indices share the same runtime length; the table is captured once.
example := (by source_fun_prop :
  HasProgram (fun x : Σ n, (Fin n → ℕ) × List (Fin n) => x.2.2.map x.2.1) _ _ _)

-- Pointwise choices must never masquerade as one implementation for all runtime lengths.
example (f : (n : ℕ) → Fin n → Bool) (program : ℕ → Value → Code Value)
    (_hf : ∀ n, HasProgram (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgram (fun x : Σ n, List (Fin n) => x.2.map (f x.1)) _ _ _)
  trivial

end DependentMap

end ComplexityTest.SourceTranslation.Traversal
