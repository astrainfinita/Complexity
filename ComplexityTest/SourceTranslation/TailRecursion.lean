/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.TailRecursion

@[expose] public section

open Complexity TreeProgram TreeProgram.Source
namespace ComplexityTest.SourceTranslation.TailRecursion

open Lean Meta Elab Tactic in
elab (name := guardTailGoals) "guard_tail_goals" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if (target.find? fun e => e.isAppOf ``TreeProgram.Source.Bounds.time ||
          e.isAppOf ``TreeProgram.Source.Bounds.peak || match e with
            | .proj ``TreeProgram.Source.Bounds _ _ => true
            | _ => false).isSome then
        throwError "tail loop left a budget field projection in a local obligation"
      if (target.find? fun e => e.isApp && e.getAppFn.isLambda).isSome then
        throwError "tail loop left a beta redex in a local obligation"
      let displayed := (← ppExpr target).pretty
      if (displayed.splitOn "TreeProgram.Source").length > 1 then
        throwError "tail loop exposed an internal certificate or budget projection"

#allow_unused_tactic! guardTailGoals

def gather : Bool × List (List Bool) × List Bool → List Bool
  | (_, [], acc) => acc
  | (tag, xs :: rest, acc) => gather (tag, rest, tag :: tag :: (xs.reverse ++ acc))
termination_by x => x.2.1.length

def advance (x : Bool × List (List Bool) × List Bool) :=
  match x.2.1 with
  | [] => x
  | xs :: rest => (x.1, rest, x.1 :: x.1 :: (xs.reverse ++ x.2.2))

abbrev GatherInput := Bool × List (List Bool) × List Bool

def chunkWork (x : GatherInput) : ℕ :=
  match x.2.1 with | [] => 1 | xs :: _ => ⌜xs⌝ₜ.size + 1

theorem hasProgram_advance : HasProgram advance hole(⊢ program) chunkWork (fun x => ⌜x⌝ₜ.size + 10) := by
  abstract_hole program using programAdvance
  fill_hole program in source_fun_prop
  all_goals
    apply Dominated.of_le_mul 20
    rintro ⟨tag, _ | ⟨xs, rest⟩, acc⟩
    · simp [chunkWork, size_encode_prod] <;> omega
    · have := size_encode_list_append xs.reverse acc
      have := length_le_codeSize xs
      have := size_encode_bool_le tag
      have := Tree.size_pos ⌜xs⌝ₜ
      simp [chunkWork, size_encode_prod] at *
      try omega

def gatherCheck (x : GatherInput) := !x.2.1.isEmpty

theorem hasProgram_gatherCheck :
    HasProgram gatherCheck hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programGatherCheck
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_gatherFinish :
    HasProgram (fun x : GatherInput => x.2.2) hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programGatherFinish
  fill_hole program in source_fun_prop

-- The invariant permits the accumulator to grow as chunks are consumed.
def gatherInvariant (x y : GatherInput) : Prop :=
  ⌜y⌝ₜ.size + 10 * y.2.1.length ≤ ⌜x⌝ₜ.size + 10 * x.2.1.length

theorem gather_input_size : Dominated
    (fun z : {p : GatherInput × GatherInput // gatherInvariant p.1 p.2} => ⌜z.1.2⌝ₜ.size)
    (fun z => ⌜z.1.1⌝ₜ.size) := by
  have hlen : Dominated
      (fun z : {p : GatherInput × GatherInput // gatherInvariant p.1 p.2} => z.1.1.2.1.length)
      (fun z => ⌜z.1.1⌝ₜ.size) := Dominated.of_le fun z => by
    rcases z with ⟨⟨⟨tag, xs, acc⟩, y⟩, hi⟩
    have h := length_le_codeSize xs
    simp only [size_encode_prod]
    omega
  apply ((Dominated.refl _).add_same (hlen.const_mul_left 10)).mono_left
  intro z
  have h := z.2
  dsimp only [gatherInvariant] at h
  omega

/-- The potential is the size of the chunks still to be consumed. -/
theorem hasProgram_gatherLoop : HasProgram gather hole(⊢ program)
    (fun x => 1 + (⌜x.2.1⌝ₜ.size + 1) + 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programGatherLoop
  fill_hole program in
    refine HasProgram.tail_loop_potential hasProgram_gatherCheck hasProgram_advance
      hasProgram_gatherFinish gatherInvariant (fun _ x => ⌜x.2.1⌝ₜ.size) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) ?_ (fun _ => le_rfl) ?_ gather_input_size gather_input_size ?_ ?_
      (Dominated.const 2) ?_
  · rintro ⟨tag, xs, acc⟩
    cases xs <;> simp [gather, gatherCheck, advance]
  · rintro ⟨xt, original, initial⟩ ⟨tag, ys, acc⟩ hi ht
    cases ys with
    | nil => simp [gatherCheck] at ht
    | cons xs rest =>
      have ha := size_encode_list_append xs.reverse acc
      simp only [size_encode_reverse] at ha
      dsimp only [gatherInvariant, advance] at *
      cases tag <;> simp only [size_encode_prod, encode_bool_false, encode_bool_true,
        encode_list_cons, size_encode_unit, List.length_cons] at hi ⊢ <;> omega
  · exact (gather_input_size.add_same (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)).comp
      (fun z : {p : GatherInput × GatherInput //
        gatherInvariant p.1 p.2 ∧ gatherCheck p.2 = true} => ⟨z.1, z.2.1⟩)
  · exact gather_input_size.comp
      (fun z : {p : GatherInput × GatherInput //
        gatherInvariant p.1 p.2 ∧ gatherCheck p.2 = false} => ⟨z.1, z.2.1⟩)
  · have h : Dominated
        (fun y : {y : GatherInput // gatherCheck y = true} => chunkWork y.1)
        (fun y => ⌜y.1.2.1⌝ₜ.size - ⌜(advance y.1).2.1⌝ₜ.size) := by
      apply Dominated.of_le
      rintro ⟨⟨tag, ys, acc⟩, ht⟩
      cases ys with
      | nil => simp [gatherCheck] at ht
      | cons xs rest => simp [chunkWork, advance, size_encode_prod]
    have hp : ∀ y : {y : GatherInput // gatherCheck y = true}, 0 < chunkWork y.1 := by
      intro y; rcases y with ⟨⟨tag, ys, acc⟩, ht⟩
      cases ys <;> simp [chunkWork]
    exact (((Dominated.refl _).add_same (Dominated.const_of_pos 1 hp)).add_same
      (Dominated.const_of_pos 1 hp) |>.trans h).comp
        (fun z : {p : GatherInput × GatherInput //
          gatherInvariant p.1 p.2 ∧ gatherCheck p.2 = true} => ⟨z.1.2, z.2.2⟩)

@[source] theorem hasProgram_gather : HasProgram gather hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programGather
  fill_hole program in
    exact hasProgram_gatherLoop.mono (Dominated.of_le_mul 4 fun ⟨tag, xs, acc⟩ => by
      have := Tree.size_pos ⌜(tag, xs, acc)⌝ₜ
      simp only [size_encode_prod] at *
      omega) (Dominated.refl _)

theorem gather_model : gather ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- The accumulator really grows; no decreasing-space condition is hidden in the interface.
example : ⌜((true, [[]], []) : GatherInput)⌝ₜ.size <
    ⌜advance (true, [[]], [])⌝ₜ.size := by decide

-- Variable rounds remain visible in the public work measure.
example : chunkWork (true, [[]], []) < chunkWork (true, [[true]], []) := by decide

example : programGather = loopCode programGatherCheck programAdvance programGatherFinish := rfl

def keep (xs : List Bool) := xs

@[source] theorem hasProgram_keep :
    HasProgram keep hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeep
  fill_hole program in
    source_fun_prop using loop
      (test := fun _ => false) (next := id) (finish := id)
      (invariant := fun x y => y = x)
      (measure := fun _ => 0) (step := fun _ => 1) (stop := fun _ => 1)
      (space := fun x => ⌜x⌝ₜ.size)
  guard_tail_goals
  case equation => intro; rfl
  case initial => intro; rfl
  case next_state => simp
  case decreases => simp
  case input_size => exact Dominated.of_le (fun z => by rw [z.2])
  case check_peak => exact Dominated.zero
  case step_peak => exact Dominated.zero
  case stop_peak => exact Dominated.zero
  case step_time => exact Dominated.zero
  case check_time => exact Dominated.const _
  case stop_time => exact Dominated.zero
  case time => exact Dominated.const _
  all_goals intro; decide

theorem keep_loop_model : keep ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- A zero allowance cannot replace the selected loop by the ordinary identity program.
example : True := by
  fail_if_success
    have : HasProgram keep hole(⊢ program) (fun _ => 0) (fun _ => 0) := by
      fill_hole program in source_fun_prop
      all_goals exact Dominated.zero
  trivial

end ComplexityTest.SourceTranslation.TailRecursion
