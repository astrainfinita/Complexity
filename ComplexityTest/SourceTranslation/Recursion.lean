/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity

namespace ComplexityTest.SourceTranslation.Recursion

open Lean Meta Elab Tactic in
elab (name := guardPublicGoals) "guard_public_goals" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      let displayed := (← ppExpr type).pretty
      if (displayed.splitOn "TreeProgram.Source").length > 1 then
        throwError "recursion exposed an internal certificate or budget in a user goal"

#allow_unused_tactic! guardPublicGoals

def invert : List Bool → List Bool
  | [] => []
  | x :: xs => (!x) :: invert xs

def invertResume (x : {xs : List Bool // (!xs.isEmpty) = true}) (result : List Bool) :=
  match h : x.val with
  | [] => False.elim (by simpa [h] using x.property)
  | a :: _ => (!a) :: result

theorem length_invert (xs : List Bool) : (invert xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [invert, List.length_cons] using congrArg Nat.succ ih

open TreeProgram.Source
open TreeProgram.Source.Internal (HasProgram)

-- The measured entry exposes source equations, without a guessed exact allowance.
def hasProgram_invert := (by
  source_fun_prop using recursion
    (test := fun xs : List Bool => !xs.isEmpty) (next := List.tail)
    (finish := fun _ => []) (resume := invertResume)
    (measure := List.length)
    (decreases := by intro xs h; cases xs <;> simp_all)
  guard_public_goals
  case finish_eq =>
    rintro ⟨xs, h⟩
    cases xs with
    | nil => rfl
    | cons => cases h
  case resume_eq =>
    rintro ⟨xs, h⟩
    cases xs with
    | nil => cases h
    | cons => rfl : HasProgram invert _ _ _)

def endPosition (xs : List Bool) : Fin (xs.length + 1) := Fin.last xs.length

def positionResume : (x : {xs : List Bool // (!xs.isEmpty) = true}) →
    Fin (x.val.tail.length + 1) → Fin (x.val.length + 1)
  | ⟨[], h⟩, _ => False.elim (by simp at h)
  | ⟨_ :: _, _⟩, result => result.succ

-- A dependent result is implemented at its own type; callbacks return ordinary Fin values.
def hasProgram_endPosition := (by
  source_fun_prop using recursion
    (test := fun xs : List Bool => !xs.isEmpty) (next := List.tail)
    (finish := fun _ => 0) (resume := positionResume)
    (measure := List.length)
    (decreases := by intro xs h; cases xs <;> simp_all)
  guard_public_goals
  case finish_eq =>
    rintro ⟨xs, h⟩
    cases xs with
    | nil => rfl
    | cons => cases h
  case resume_eq =>
    rintro ⟨xs, h⟩
    cases xs with
    | nil => cases h
    | cons => rfl : HasProgram endPosition _ _ _)

-- An unsupported callback fails before changing the selected source goal.
example : HasProgram (id : List Bool → List Bool) hole(⊢ program) (fun _ => 0) (fun _ => 0) := by
  fail_if_success
    source_fun_prop using recursion
      (test := fun xs => !xs.isEmpty) (next := fun xs => invert xs.tail)
      (finish := fun x => x.val) (resume := fun x _ => x.val)
      (measure := List.length)
      (decreases := by intro xs h; rw [length_invert]; cases xs <;> simp_all)
  fill_hole program in source_fun_prop

def drain : List Bool → Unit
  | [] => ()
  | _ :: xs => drain xs

def drainRecursion : TreeProgram.Source.Recursion drain where
  test xs := !xs.isEmpty
  next := List.tail
  finish _ := ()
  resume _ _ := ()
  finish_eq := by intros; exact Subsingleton.elim _ _
  resume_eq := by intros; exact Subsingleton.elim _ _
  measure := List.length
  decreases := by intro xs h; cases xs <;> simp_all

theorem hasProgramIn_drainFinish :
    HasProgramIn drainRecursion.finish hole(⊢ program) IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programDrainFinish
  fill_hole program in source_fun_prop

theorem hasProgramIn_drainResume : HasProgramIn
    (fun x : drainRecursion.Return => drainRecursion.resume x.1 x.2) hole(⊢ program) IsO(fun _ => 1)
    IsO(fun _ => 1) := by
  abstract_hole program using programDrainResume
  fill_hole program in source_fun_prop

-- Callback growths enter the structural cost directly. No coefficient is selected in induction.
private theorem drain_cost_growth :
    let bc : Bounds (List Bool) := ⟨fun _ => 1, fun xs => ⌜xs⌝ₜ.size⟩
    let bd : Bounds {xs // drainRecursion.test xs = false} := ⟨fun _ => 1, fun _ => 1⟩
    let br : Bounds drainRecursion.Return := ⟨fun _ => 1, fun _ => 1⟩
    Dominated (fun xs => (drainRecursion.cost bc bc bd br xs).time) (fun xs => xs.length + 1) ∧
    Dominated (fun xs => (drainRecursion.cost bc bc bd br xs).peak)
      (fun xs => ⌜xs⌝ₜ.size + (xs.length + 1) * (⌜xs⌝ₜ.size + 1)) := by
  dsimp only
  let I (xs ys : List Bool) := ⌜ys⌝ₜ.size ≤ ⌜xs⌝ₜ.size
  have hsize : Dominated
      (fun z : {p : List Bool × List Bool // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => ⌜z.1.1⌝ₜ.size) := Dominated.of_le fun z => z.2
  simpa only [drainRecursion, Nat.mul_one, id_eq] using
    drainRecursion.dominated_cost_of_bounds
      ⟨fun _ => 1, fun xs => ⌜xs⌝ₜ.size⟩ ⟨fun _ => 1, fun xs => ⌜xs⌝ₜ.size⟩
      ⟨fun _ => 1, fun _ => 1⟩ ⟨fun _ => 1, fun _ => 1⟩
      I id (fun xs => ⌜xs⌝ₜ.size) (fun _ => 1) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size)
      (fun _ => le_rfl)
      (fun xs ys hi _ => (show ⌜ys.tail⌝ₜ.size ≤ ⌜ys⌝ₜ.size by cases ys <;> simp).trans hi)
      hsize hsize hsize
      (Dominated.const_of_pos 1 fun _ => Tree.size_pos _)
      (Dominated.const_of_pos 1 fun _ => Tree.size_pos _)
      (Dominated.refl _) (Dominated.refl _) (Dominated.refl _) (Dominated.refl _)
      (fun _ => Nat.zero_lt_one) (fun _ => Nat.zero_lt_one)

/-- The test of `drain`, translated as `Bool.not` after `List.isEmpty`. -/
theorem hasProgramIn_drainTest :
    HasProgramIn (fun xs : List Bool => !xs.isEmpty) hole(⊢ program) IsO(fun _ => 1)
    IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDrainTest
  fill_hole program in source_fun_prop

-- The terminal allowance appears once; the stack allowance grows with recursion depth.
theorem hasProgramIn_drainStructural : HasProgramIn drain hole(⊢ program)
    IsO(fun xs => 1 + (xs.length + 1) + 1)
    IsO(fun xs => (⌜xs⌝ₜ.size + (xs.length + 1) * (⌜xs⌝ₜ.size + 1)) + 1) := by
  abstract_hole program using programDrainStructural
  refine HasProgram.toHasProgramIn ?_
  fill_hole program in
    exact (drainRecursion.hasProgram hasProgramIn_drainTest.toHasProgram
      List.hasProgramIn_tail.toHasProgram hasProgramIn_drainFinish.toHasProgram
      hasProgramIn_drainResume.toHasProgram).mono
      (((Dominated.refl _).add drain_cost_growth.1).add (Dominated.refl _))
      (drain_cost_growth.2.add (Dominated.refl _))

-- The automatic entry builds the same recursive program from the same callbacks.
example := (by
    source_fun_prop using recursion
      (test := fun xs : List Bool => !xs.isEmpty) (next := List.tail)
      (finish := fun _ => ()) (resume := fun _ _ => ())
      (measure := List.length)
      (decreases := by intro xs h; cases xs <;> simp_all)
    all_goals intros; exact Subsingleton.elim _ _ : HasProgram drain programDrainStructural _ _)

@[program] theorem hasProgramIn_drain : HasProgramIn drain hole(⊢ program)
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size ^ 2) := by
  abstract_hole program using programDrain
  refine HasProgram.toHasProgramIn ?_
  have hlen : Dominated (List.length : List Bool → ℕ) (fun xs => ⌜xs⌝ₜ.size) :=
    Dominated.of_le length_le_codeSize
  have hpos (xs : List Bool) : 0 < ⌜xs⌝ₜ.size := Tree.size_pos _
  have hc : Dominated (fun _ : List Bool => 1) (fun xs => ⌜xs⌝ₜ.size) := Dominated.one hpos
  have hs := (hlen.add_same hc).mul ((Dominated.refl _).add_same hc)
  simp only [← pow_two] at hs
  fill_hole program in apply hasProgramIn_drainStructural.toHasProgram.mono
  · simp only [Dominated.add_iff]
    exact ⟨⟨hc, hlen, hc⟩, hc⟩
  · simp only [Dominated.add_iff]
    exact ⟨⟨(Dominated.refl _).le_pow (by decide), hs⟩, hc.le_pow (by decide)⟩

theorem drain_model : drain ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 2) := by
  model_fun_prop

-- A terminal callback is paid only in the stop equation, not at every recursive step.
example (bc bs : Bounds (List Bool))
    (bd : Bounds {xs // drainRecursion.test xs = false}) (br : Bounds drainRecursion.Return) :
    (drainRecursion.cost bc bs bd br []).time = bd.time ⟨[], rfl⟩ + 2 := by
  rw [drainRecursion.cost_stop bc bs bd br [] rfl]

-- General recursion saves the caller's data in addition to the recursive tail's peak.
example (bc bs : Bounds (List Bool))
    (bd : Bounds {xs // drainRecursion.test xs = false}) (br : Bounds drainRecursion.Return)
    (a : Bool) (xs : List Bool) :
    (drainRecursion.cost bc bs bd br xs).peak + ⌜a :: xs⌝ₜ.size + 1 ≤
      (drainRecursion.cost bc bs bd br (a :: xs)).peak := by
  rw [drainRecursion.cost_step bc bs bd br (a :: xs) rfl]
  exact (Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans
    (Nat.le_max_right ..)))

-- A different explicitly requested program can compute this function in constant time.
example : drain ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop via (fun _ : List Bool => ())
  case source_eq => funext xs; exact Subsingleton.elim _ _

end ComplexityTest.SourceTranslation.Recursion
