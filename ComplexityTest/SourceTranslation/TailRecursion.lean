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

noncomputable def advanceImplementation : Implementation advance := by source_fun_prop

@[source_growth] theorem advance_growth : advanceImplementation.HasGrowth
    chunkWork (fun x => ⌜x⌝ₜ.size + 10) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover (fun x : Bool × List Bool => (x.1, [], x.2))
      (fun x : Bool × List Bool × List (List Bool) × List Bool => (x.1, x.2.1 :: x.2.2.1, x.2.2.2))
      (by rintro ⟨tag, xs, acc⟩; cases xs with
          | nil => exact Or.inl ⟨(tag, acc), rfl⟩
          | cons head tail => exact Or.inr ⟨(tag, head, tail, acc), rfl⟩)
  all_goals
    simp only [Function.comp_def, chunkWork, size_encode_prod,
      encode_list_cons, List.length_reverse, size_encode_reverse]
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff,
      Nat.ofNat_pos]
  all_goals repeat' apply And.intro
  all_goals first
    | exact Dominated.const _
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => by positivity)
    | (exact (Implementation.hasGrowth_reverse.1.comp
         (fun x : Bool × List Bool × List (List Bool) × List Bool => x.2.1)).mono
         (fun x => by simp only [Function.comp_apply]; omega))
    | (exact (Implementation.hasGrowth_reverse.2.comp
         (fun x : Bool × List Bool × List (List Bool) × List Bool => x.2.1)).mono
         (fun x => by simp only [Function.comp_apply]; omega))
    | (apply Dominated.of_le; intro x
       have h := length_le_codeSize x.2.1
       omega)
    | (apply Dominated.of_le; rintro ⟨tag, acc⟩
       dsimp only
       omega)
    | (apply Dominated.of_le; rintro ⟨tag, head, tail, acc⟩
       dsimp only
       have h := size_encode_list_append head.reverse acc
       have hb := size_encode_bool_le tag
       simp only [size_encode_reverse] at h
       omega)

def gatherCheck (x : GatherInput) := !x.2.1.isEmpty
noncomputable def gatherCheckImplementation : Implementation gatherCheck := by source_fun_prop
@[source_growth] theorem gatherCheck_growth : gatherCheckImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals simp only [Dominated.add_iff, Dominated.max_iff]
  all_goals repeat' apply And.intro
  all_goals first
    | exact Dominated.const _
    | (apply Dominated.of_le; rintro ⟨tag, xs, acc⟩
       have hb := size_encode_bool_le xs.isEmpty
       have hn := size_encode_bool_le (Bool.rec true false xs.isEmpty)
       have hp := Tree.size_pos ⌜xs⌝ₜ
       simp only [size_encode_prod]; omega)

noncomputable def gatherFinishImplementation : Implementation (fun x : GatherInput => x.2.2) := by
  source_fun_prop
@[source_growth] theorem gatherFinish_growth : gatherFinishImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals simp only [Dominated.add_iff, Dominated.max_iff]
  all_goals repeat' apply And.intro
  all_goals first
    | exact Dominated.const _
    | (apply Dominated.of_le; rintro ⟨tag, xs, acc⟩
       have hb := size_encode_bool_le xs.isEmpty
       have hn := size_encode_bool_le (Bool.rec true false xs.isEmpty)
       have hp := Tree.size_pos ⌜xs⌝ₜ
       simp only [size_encode_prod]; omega)

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

noncomputable def gatherPlan : TailPotentialGrowth gatherCheckImplementation
    advanceImplementation gatherFinishImplementation gather := by
  refine TailPotentialGrowth.ofGrowth ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    ⟨chunkWork, fun x => ⌜x⌝ₜ.size + 10⟩ ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    gatherCheck_growth advance_growth gatherFinish_growth gatherInvariant
    (fun _ x => ⌜x.2.1⌝ₜ.size) (fun _ => 1) (fun x => ⌜x⌝ₜ.size)
    ?_ (fun _ => le_rfl) ?_ gather_input_size gather_input_size ?_ gather_input_size ?_ ?_
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
  · exact gather_input_size.add_same (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)
  · exact Dominated.const 2
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

noncomputable def gatherImplementation : Implementation gather := gatherPlan.implementation

@[source_growth] theorem gather_growth : gatherImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  apply gatherPlan.hasGrowth.mono
  · have hc : Dominated gatherCheckImplementation.bounds.time (fun x => ⌜x⌝ₜ.size) :=
      gatherCheck_growth.1.trans (Dominated.const_of_pos 1 fun _ => Tree.size_pos _)
    have hp : Dominated (fun x : GatherInput => ⌜x.2.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le fun ⟨tag, xs, acc⟩ => by simp only [size_encode_prod]; omega
    exact (hc.add_same (hp.add_same (Dominated.const_of_pos 1 fun _ => Tree.size_pos _))).add_same
      (Dominated.const_of_pos 4 fun _ => Tree.size_pos _)
  · exact Dominated.refl _

@[source] theorem gather_model : gather ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) :=
  (by simpa only [pow_one] using gather_growth :
    gatherImplementation.HasGrowth (fun x => ⌜x⌝ₜ.size ^ 1) (fun x => ⌜x⌝ₜ.size ^ 1)).mem_ftisp_pow
      (by decide)

-- The accumulator really grows; no decreasing-space condition is hidden in the interface.
example : ⌜((true, [[]], []) : GatherInput)⌝ₜ.size <
    ⌜advance (true, [[]], [])⌝ₜ.size := by decide

-- Variable rounds remain visible both in the public work measure and the semantic allowance.
example : chunkWork (true, [[]], []) < chunkWork (true, [[true]], []) := by decide
example : advanceImplementation.bounds.time (true, [[]], []) <
    advanceImplementation.bounds.time (true, [[true]], []) := by decide

example : gatherImplementation.program = loopCode gatherCheckImplementation.program
    advanceImplementation.program gatherFinishImplementation.program := rfl

def keep (xs : List Bool) := xs

noncomputable def keepImplementation : Implementation keep := by
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
  all_goals intro; decide

@[source_growth] theorem keep_growth : keepImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · dsimp only
    exact Dominated.const _
  · exact Dominated.refl _

@[source] theorem keep_loop_model : keep ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  exact (show keepImplementation.HasGrowth (fun x => ⌜x⌝ₜ.size ^ 0)
        (fun x => ⌜x⌝ₜ.size ^ 1) from by simpa only [pow_zero, pow_one] using keep_growth).mem_ftisp_pow
      (by decide)

-- A zero allowance cannot replace the selected loop by the ordinary identity program.
example : True := by
  fail_if_success
    have : keepImplementation.HasGrowth (fun _ => 0) (fun _ => 0) := by source_fun_prop
  trivial

end ComplexityTest.SourceTranslation.TailRecursion
