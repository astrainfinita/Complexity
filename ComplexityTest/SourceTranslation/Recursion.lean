/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import Complexity.Tactic.TreeProgram.Recursion

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Recursion

private def continues (xs : List Bool) := !xs.isEmpty

private def invert : List Bool → List Bool
  | [] => []
  | x :: xs => (!x) :: invert xs

private def invertRecursion : Source.Recursion invert where
  test := continues
  next := List.tail
  finish _ := []
  resume x result :=
    match h : x.1 with
    | [] => False.elim (by simpa [continues, h] using x.2)
    | a :: _ => (!a) :: result
  finish_eq := by
    rintro ⟨xs, h⟩
    cases xs <;> dsimp [continues] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨xs, h⟩
    cases xs <;> dsimp [continues] at h ⊢ <;> first | contradiction | rfl
  measure := List.length
  decreases := by intro xs h; cases xs <;> simp_all [continues]

private noncomputable def checkImpl : Implementation invertRecursion.test := by source_fun_prop
private def nextImpl : Implementation invertRecursion.next := by source_fun_prop
private noncomputable def finishImpl : Implementation (fun x => ⌜invertRecursion.finish x⌝ₜ) := by
  source_fun_prop
private noncomputable def resumeImpl : Implementation
    (fun x : invertRecursion.Return => ⌜invertRecursion.resume x.1 x.2⌝ₜ) := by source_fun_prop

private noncomputable def invertImpl :=
  invertRecursion.implementation checkImpl nextImpl finishImpl resumeImpl

example : Realizes (fun xs => ⌜invert xs⌝ₜ)
    (invertRecursion.bounds checkImpl.bounds nextImpl.bounds finishImpl.bounds resumeImpl.bounds) :=
  invertImpl.realizes

private def endPosition (xs : List Bool) : Fin (xs.length + 1) := Fin.last xs.length

-- The recursive return inhabits a different Fin type; no runtime index check is added.
private def positionRecursion : Source.Recursion endPosition where
  test := continues
  next := List.tail
  finish _ := 0
  resume
    | ⟨[], h⟩, _ => False.elim (by simp [continues] at h)
    | ⟨_ :: _, _⟩, result => result.succ
  finish_eq := by
    rintro ⟨xs, h⟩
    cases xs <;> dsimp [continues] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨xs, h⟩
    cases xs <;> dsimp [continues] at h ⊢ <;> first | contradiction | rfl
  measure := List.length
  decreases := by intro xs h; cases xs <;> simp_all [continues]

private noncomputable def positionFinish : Implementation
    (fun x => ⌜positionRecursion.finish x⌝ₜ) := by source_fun_prop
private noncomputable def positionResume : Implementation
    (fun x : positionRecursion.Return => ⌜positionRecursion.resume x.1 x.2⌝ₜ) := by source_fun_prop

private noncomputable def positionImpl : Implementation (fun xs => ⌜endPosition xs⌝ₜ) :=
  positionRecursion.implementation checkImpl nextImpl positionFinish positionResume

example : Realizes (fun xs => ⌜endPosition xs⌝ₜ) positionImpl.bounds := positionImpl.realizes

end ComplexityTest.SourceTranslation.Recursion
