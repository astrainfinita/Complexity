/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Translation

/-! # Source-guided tail loops

Callbacks are selected once. Remaining time pays for the next round or the final result;
space bounds every reachable state relative to the initial input, without a saved-call stack.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

/-- Source equations discharge the loop's functional invariant. Time itself proves termination. -/
theorem Implements.tailLoop {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {pc ps pd : TreeProgram.Value → TreeProgram.Code TreeProgram.Value}
    {test : α → Bool} {next : α → α} {finish result : α → β} {bc bs bd : Bounds α}
    (hc : Implements pc test bc) (hs : Implements ps next bs) (hd : Implements pd finish bd)
    (I : α → α → Prop) (time : α → α → ℕ) (space : α → ℕ)
    (equation : ∀ y, result y = if test y then result (next y) else finish y)
    (initial : ∀ x, I x x)
    (input_size : ∀ x y, I x y → result y = result x → ⌜y⌝ₜ.size ≤ space x)
    (check_space : ∀ x y, I x y → result y = result x → bc.peak y ≤ space x)
    (stop_bounds : ∀ x y, I x y → result y = result x → test y = false →
      bd.time y + 2 ≤ time x y ∧ bd.peak y ≤ space x)
    (step_bounds : ∀ x y, I x y → result y = result x → test y = true →
      bs.peak y ≤ space x ∧ I x (next y) ∧
        bs.time y + bc.time (next y) + 6 + time x (next y) ≤ time x y) :
    Implements (loopCode pc ps pd) result ⟨fun x => bc.time x + time x x + 4, space⟩ := by
  apply hc.loop_budget_finish hs hd (fun x y => I x y ∧ result y = result x) time space
    (fun x => ⟨initial x, rfl⟩) (fun x y h => input_size x y h.1 h.2)
    (fun x y h => check_space x y h.1 h.2)
    (fun x y h ht => (stop_bounds x y h.1 h.2 ht).1) ?_ ?_
  · intro x y hi ht
    obtain ⟨hp, hi', hb⟩ := step_bounds x y hi.1 hi.2 ht
    refine ⟨hp, ⟨hi', ?_⟩, hb⟩
    simpa only [ht, ↓reduceIte] using (equation y).symm.trans hi.2
  · intro x y hi ht
    refine ⟨(stop_bounds x y hi.1 hi.2 ht).2, ?_⟩
    simpa only [ht, Bool.false_eq_true, ↓reduceIte] using (equation y).symm.trans hi.2

end Complexity.TreeProgram.Source


namespace Complexity.TreeProgram.Source

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {test : α → Bool} {next : α → α} {finish result : α → β}

/-- Growth estimates for all states reachable from all initial inputs, as one callback family. -/
structure TailGrowth (hc : Implementation test) (hs : Implementation next)
    (hd : Implementation finish) (result : α → β) where
  invariant : α → α → Prop
  measure : α → ℕ
  step : α → ℕ
  stop : α → ℕ
  peak : α → ℕ
  equation : ∀ y, result y = if test y then result (next y) else finish y
  initial : ∀ x, invariant x x
  next_state : ∀ x y, invariant x y → test y = true → invariant x (next y)
  decreases : ∀ x y, invariant x y → test y = true → measure (next y) < measure y
  input_size : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} => ⌜z.1.2⌝ₜ.size) (fun z => peak z.1.1)
  local_peak : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} =>
      max (hc.bounds.peak z.1.2)
        (if test z.1.2 then hs.bounds.peak z.1.2 else hd.bounds.peak z.1.2))
    (fun z => peak z.1.1)
  stop_time : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} =>
      if test z.1.2 then 0 else hd.bounds.time z.1.2 + 2) (fun z => stop z.1.1)
  round_time : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} =>
      if test z.1.2 then hs.bounds.time z.1.2 + hc.bounds.time (next z.1.2) + 6 else 0)
    (fun z => step z.1.1)

/-- A remaining-work potential permits different costs in different rounds. The one coefficient
in `round_time` covers every reachable state of every initial input. -/
structure TailPotentialGrowth (hc : Implementation test) (hs : Implementation next)
    (hd : Implementation finish) (result : α → β) where
  invariant : α → α → Prop
  potential : α → α → ℕ
  stop : α → ℕ
  peak : α → ℕ
  equation : ∀ y, result y = if test y then result (next y) else finish y
  initial : ∀ x, invariant x x
  next_state : ∀ x y, invariant x y → test y = true → invariant x (next y)
  input_size : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} => ⌜z.1.2⌝ₜ.size) (fun z => peak z.1.1)
  local_peak : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} => max (hc.bounds.peak z.1.2)
      (if test z.1.2 then hs.bounds.peak z.1.2 else hd.bounds.peak z.1.2))
    (fun z => peak z.1.1)
  stop_time : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} =>
      if test z.1.2 then 0 else hd.bounds.time z.1.2 + 2) (fun z => stop z.1.1)
  round_time : Dominated
    (fun z : {p : α × α // invariant p.1 p.2} =>
      if test z.1.2 then hs.bounds.time z.1.2 + hc.bounds.time (next z.1.2) + 6 else 0)
    (fun z => potential z.1.1 z.1.2 - potential z.1.1 (next z.1.2))

namespace TailPotentialGrowth

variable {hc : Implementation test} {hs : Implementation next} {hd : Implementation finish}
  (h : TailPotentialGrowth hc hs hd result)

theorem exists_bounds_implements : ∃ b : Bounds α,
    Implements (loopCode hc.program hs.program hd.program) result b ∧
      Dominated b.time (fun x => (hc.bounds.time x + (h.potential x x + h.stop x)) + 4) ∧
      Dominated b.peak h.peak := by
  obtain ⟨Cs, hsize⟩ := h.input_size
  obtain ⟨Cp, hpeak⟩ := h.local_peak
  obtain ⟨Ct, hstop⟩ := h.stop_time
  obtain ⟨Cr, hround⟩ := h.round_time
  simp only [Nat.nsmul_eq_mul] at hsize hpeak hstop hround
  let time (x y : α) := Cr * h.potential x y + Ct * h.stop x
  let space (x : α) := (Cs + Cp) * h.peak x
  refine ⟨⟨fun x => hc.bounds.time x + time x x + 4, space⟩, ?_, ?_, ?_⟩
  · apply hc.implements.tailLoop hs.implements hd.implements h.invariant time space
      h.equation h.initial
    · intro x y hi _
      exact (hsize ⟨(x, y), hi⟩).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · intro x y hi _
      exact ((Nat.le_max_left _ _).trans (hpeak ⟨(x, y), hi⟩)).trans
        (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
    · intro x y hi _ ht
      have ht' := hstop ⟨(x, y), hi⟩
      have hp' := hpeak ⟨(x, y), hi⟩
      simp only [ht, Bool.false_eq_true, ↓reduceIte, Nat.max_le] at ht' hp'
      exact ⟨ht'.trans (Nat.le_add_left _ _), hp'.2.trans
        (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))⟩
    · intro x y hi _ ht
      have hr := hround ⟨(x, y), hi⟩
      have hp := hpeak ⟨(x, y), hi⟩
      simp only [ht, ↓reduceIte, Nat.max_le] at hr hp
      refine ⟨hp.2.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)),
        h.next_state x y hi ht, ?_⟩
      have hmono : h.potential x (next y) ≤ h.potential x y := by
        by_contra hn
        have hz : h.potential x y - h.potential x (next y) = 0 := Nat.sub_eq_zero_of_le (by omega)
        rw [hz, Nat.mul_zero] at hr
        omega
      have heq := Nat.mul_add Cr (h.potential x y - h.potential x (next y)) (h.potential x (next y))
      rw [Nat.sub_add_cancel hmono] at heq
      dsimp only [time]
      omega
  · exact (Dominated.refl hc.bounds.time).add
      (((Dominated.refl (fun x => h.potential x x)).const_mul_left Cr).add
        ((Dominated.refl h.stop).const_mul_left Ct)) |>.add (Dominated.refl (fun _ => 4))
  · exact (Dominated.refl h.peak).const_mul_left (Cs + Cp)

/-- The program is fixed by the callbacks, independently of the potential's coefficient. -/
noncomputable def implementation : Implementation result :=
  Implementation.ofImplements (loopCode hc.program hs.program hd.program)
    h.exists_bounds_implements.choose h.exists_bounds_implements.choose_spec.1

theorem program_implementation :
    h.implementation.program = loopCode hc.program hs.program hd.program := rfl

theorem hasGrowth : h.implementation.HasGrowth
    (fun x => (hc.bounds.time x + (h.potential x x + h.stop x)) + 4) h.peak :=
  h.exists_bounds_implements.choose_spec.2

/-- Consume the selected callbacks' specifications. A unit of work pays for controller
overhead; the library unifies its coefficient with the callback coefficients. -/
def ofGrowth (bc bs bd : Bounds α)
    (gc : hc.HasGrowth bc.time bc.peak) (gs : hs.HasGrowth bs.time bs.peak)
    (gd : hd.HasGrowth bd.time bd.peak)
    (I : α → α → Prop) (potential : α → α → ℕ) (stop peak : α → ℕ)
    (equation : ∀ y, result y = if test y then result (next y) else finish y)
    (initial : ∀ x, I x x)
    (next_state : ∀ x y, I x y → test y = true → I x (next y))
    (input_size : Dominated (fun z : {p : α × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (check_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bc.peak z.1.2)
      (fun z => peak z.1.1))
    (step_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bs.peak z.1.2)
      (fun z => peak z.1.1))
    (stop_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bd.peak z.1.2)
      (fun z => peak z.1.1))
    (stop_time : Dominated
      (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = false} => bd.time z.1.2 + 1)
      (fun z => stop z.1.1))
    (round_time : Dominated
      (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = true} =>
        bs.time z.1.2 + bc.time (next z.1.2) + 1)
      (fun z => potential z.1.1 z.1.2 - potential z.1.1 (next z.1.2))) :
    TailPotentialGrowth hc hs hd result where
  invariant := I
  potential := potential
  stop := stop
  peak := peak
  equation := equation
  initial := initial
  next_state := next_state
  input_size := input_size
  local_peak := by
    have hc := (gc.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans check_peak
    have hs := (gs.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans step_peak
    have hd := (gd.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans stop_peak
    apply (hc.max_same (hs.max_same hd)).mono_left
    intro z
    dsimp only [Function.comp_apply]
    split <;> omega
  stop_time := by
    apply Dominated.of_cases (fun z => test z.1.2 = false)
    · let f (z : {z : {p : α × α // I p.1 p.2} // test z.1.2 = false}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = false} := ⟨z.1.1, z.1.2, z.2⟩
      have hd := (gd.1.comp (fun z => (f z).1.2)).add (Dominated.const 2)
      have h := hd.trans (stop_time.comp f)
      apply h.mono_left
      intro z
      simp only [Function.comp_def, f, z.2, Bool.false_eq_true, ↓reduceIte, le_refl]
    · apply Dominated.of_le
      intro z
      have ht : test z.1.1.2 = true := Bool.eq_true_of_not_eq_false z.2
      change (if test z.1.1.2 = true then 0 else _) ≤ _
      rw [ite_eq_left ht]
      exact Nat.zero_le _
  round_time := by
    apply Dominated.of_cases (fun z => test z.1.2 = true)
    · let f (z : {z : {p : α × α // I p.1 p.2} // test z.1.2 = true}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = true} := ⟨z.1.1, z.1.2, z.2⟩
      have hs := gs.1.comp (fun z => (f z).1.2)
      have hc := gc.1.comp (fun z => next (f z).1.2)
      have h := ((hs.add hc).add (Dominated.const 6)).trans (round_time.comp f)
      apply h.mono_left
      intro z
      simp only [Function.comp_def, f, z.2, ↓reduceIte, le_refl]
    · apply Dominated.of_le
      intro z
      change (if test z.1.1.2 = true then _ else 0) ≤ _
      rw [ite_eq_right z.2]
      exact Nat.zero_le _

end TailPotentialGrowth

namespace TailGrowth

variable {hc : Implementation test} {hs : Implementation next} {hd : Implementation finish}
  (h : TailGrowth hc hs hd result)

/-- A decreasing measure with one round allowance is the potential consisting of the
remaining number of rounds times the initial input's allowance. -/
def toTailPotentialGrowth : TailPotentialGrowth hc hs hd result where
  invariant := h.invariant
  potential x y := h.measure y * h.step x
  stop := h.stop
  peak := h.peak
  equation := h.equation
  initial := h.initial
  next_state := h.next_state
  input_size := h.input_size
  local_peak := h.local_peak
  stop_time := h.stop_time
  round_time := by
    apply Dominated.of_cases (fun z => test z.1.2 = true)
    · apply (h.round_time.comp Subtype.val).mono
      intro z
      change h.step z.1.1.1 ≤
        h.measure z.1.1.2 * h.step z.1.1.1 - h.measure (next z.1.1.2) * h.step z.1.1.1
      rw [← Nat.sub_mul]
      have hm : 1 ≤ h.measure z.1.1.2 - h.measure (next z.1.1.2) := by
        have := h.decreases z.1.1.1 z.1.1.2 z.1.2 z.2
        omega
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (h.step z.1.1.1) hm
    · apply Dominated.of_le
      intro z
      change (if test z.1.1.2 = true then _ else 0) ≤ _
      rw [ite_eq_right z.2]
      exact Nat.zero_le _

/-- Use the common potential certificate for the already selected callbacks. -/
noncomputable def implementation : Implementation result :=
  h.toTailPotentialGrowth.implementation

theorem program_implementation :
    h.implementation.program = loopCode hc.program hs.program hd.program := rfl

theorem hasGrowth : h.implementation.HasGrowth
    (fun x => (hc.bounds.time x + (h.measure x * h.step x + h.stop x)) + 4) h.peak :=
  h.toTailPotentialGrowth.hasGrowth

end TailGrowth

namespace Implementation

variable (hc : Implementation test) (hs : Implementation next) (hd : Implementation finish)
  (bc bs bd : Bounds α)
  (gc : hc.HasGrowth bc.time bc.peak)
  (gs : hs.HasGrowth bs.time bs.peak)
  (gd : hd.HasGrowth bd.time bd.peak)
  (I : α → α → Prop) (measure step stop peak : α → ℕ)
  (equation : ∀ y, result y = if test y then result (next y) else finish y)
  (initial : ∀ x, I x x)
  (next_state : ∀ x y, I x y → test y = true → I x (next y))
  (decreases : ∀ x y, I x y → test y = true → measure (next y) < measure y)
  (input_size : Dominated (fun z : {p : α × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
    (fun z => peak z.1.1))
  (check_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bc.peak z.1.2)
    (fun z => peak z.1.1))
  (step_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bs.peak z.1.2)
    (fun z => peak z.1.1))
  (stop_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => bd.peak z.1.2)
    (fun z => peak z.1.1))
  (step_time : Dominated (fun z : {p : α × α // I p.1 p.2} => bs.time z.1.2)
    (fun z => step z.1.1))
  (check_time : Dominated (fun z : {p : α × α // I p.1 p.2} => bc.time (next z.1.2))
    (fun z => step z.1.1))
  (stop_time : Dominated (fun z : {p : α × α // I p.1 p.2} => bd.time z.1.2)
    (fun z => stop z.1.1))
  (step_pos : ∀ x, 0 < step x) (stop_pos : ∀ x, 0 < stop x)

/-- Adapt selected callback specifications to the original tail-loop accounting theorem.
All coefficients range over the whole invariant family, and are fixed before iteration. -/
def tailLoopBounds : TailGrowth hc hs hd result where
  invariant := I
  measure := measure
  step := step
  stop := stop
  peak := peak
  equation := equation
  initial := initial
  next_state := next_state
  decreases := decreases
  input_size := input_size
  local_peak := by
    have hc := (gc.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans check_peak
    have hs := (gs.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans step_peak
    have hd := (gd.2.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans stop_peak
    apply (hc.max_same (hs.max_same hd)).mono_left
    intro z
    dsimp only [Function.comp_apply]
    split <;> omega
  stop_time := by
    have hd := (gd.1.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans stop_time
    apply (hd.add_same (Dominated.const_of_pos 2 fun z => stop_pos z.1.1)).mono_left
    intro z
    dsimp only [Function.comp_apply]
    split <;> omega
  round_time := by
    have hs := (gs.1.comp (fun z : {p : α × α // I p.1 p.2} => z.1.2)).trans step_time
    have hc := (gc.1.comp (fun z : {p : α × α // I p.1 p.2} => next z.1.2)).trans check_time
    apply ((hs.add_same hc).add_same
      (Dominated.const_of_pos 6 fun z => step_pos z.1.1)).mono_left
    intro z
    dsimp only [Function.comp_apply]
    split <;> omega

/-- The selected callbacks determine the program; growth proofs only certify its allowance. -/
noncomputable def tailLoop : Implementation result :=
  (tailLoopBounds hc hs hd bc bs bd gc gs gd I measure step stop peak equation initial
    next_state decreases input_size check_peak step_peak stop_peak step_time check_time stop_time
    step_pos stop_pos).implementation

@[source_growth] theorem hasGrowth_tailLoop :
    (tailLoop hc hs hd bc bs bd gc gs gd I measure step stop peak equation initial
      next_state decreases input_size check_peak step_peak stop_peak step_time check_time stop_time
      step_pos stop_pos).HasGrowth
      (fun x => (bc.time x + (measure x * step x + stop x)) + 4) peak := by
  apply (tailLoopBounds hc hs hd bc bs bd gc gs gd I measure step stop peak equation initial
    next_state decreases input_size check_peak step_peak stop_peak step_time check_time stop_time
    step_pos stop_pos).hasGrowth.mono
  · exact (gc.1.add (Dominated.refl _)).add (Dominated.refl _)
  · exact Dominated.refl _

theorem program_tailLoop :
    (tailLoop hc hs hd bc bs bd gc gs gd I measure step stop peak equation initial
      next_state decreases input_size check_peak step_peak stop_peak step_time check_time stop_time
      step_pos stop_pos).program = loopCode hc.program hs.program hd.program := rfl

end Implementation

end Complexity.TreeProgram.Source

end

public meta section

namespace Complexity.TreeProgram.Source

/-- A measured loop separates per-round work from its single terminal call. -/
declare_syntax_cat sourceMeasuredLoop
syntax "loop" " (" &"test" " := " term ")" " (" &"next" " := " term ")"
  " (" &"finish" " := " term ")" " (" &"invariant" " := " term ")"
  " (" &"measure" " := " term ")" " (" &"step" " := " term ")"
  " (" &"stop" " := " term ")" " (" &"space" " := " term ")" : sourceMeasuredLoop
syntax "model_fun_prop" " using " sourceMeasuredLoop (" using " ident)? : tactic
syntax "source_fun_prop" " using " sourceMeasuredLoop (" using " ident)? : tactic

open Lean Meta Elab Tactic in
private def proveMeasuredLoop (method : TSyntax `sourceMeasuredLoop) (scope : Option Ident) :
    TacticM (Array Ident × Bool × Lean.Expr × List MVarId) := withMainContext do
  let `(sourceMeasuredLoop| loop (test := $test) (next := $next) (finish := $finish)
    (invariant := $inv) (measure := $measure) (step := $step) (stop := $stop) (space := $peak)) :=
    method | throwUnsupportedSyntax
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let args := (← instantiateMVars (← goal.getType)).getAppArgs
  let source := args[4]!
  let domain := args[0]!
  let test ← elabTermEnsuringType test (← mkArrow domain (mkConst ``Bool))
  let next ← elabTermEnsuringType next (← mkArrow domain domain)
  let finish ← elabTermEnsuringType finish (← inferType source)
  let inv ← elabTermEnsuringType inv (← mkArrow domain (← mkArrow domain (mkSort .zero)))
  let budgetType ← mkArrow domain (mkConst ``Nat)
  let measure ← elabTermEnsuringType measure budgetType
  let step ← elabTermEnsuringType step budgetType
  let stop ← elabTermEnsuringType stop budgetType
  let peak ← elabTermEnsuringType peak budgetType
  Term.synthesizeSyntheticMVarsNoPostponing
  let mut callbacks := #[]
  let mut bounds := #[]
  let mut specs := #[]
  for callback in #[test, next, finish] do
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[callback])
    setGoals [g.mvarId!]
    evalTactic (← `(tactic| source_fun_prop $[using $scope:ident]?))
    let impl ← instantiateMVars g
    if impl.hasExprMVar || impl.hasSorry then
      throwError "source loop: a selected callback has unfinished obligations"
    setGoals [goal]
    let (b, h) ← calculateSourceBounds impl
    callbacks := callbacks.push impl
    bounds := bounds.push b
    specs := specs.push h
  let parameters := args[:4].toArray ++ #[test, next, finish, source] ++ callbacks ++ bounds ++
    specs ++ #[inv, measure, step, stop, peak]
  let mut result ← mkAppOptM ``Implementation.tailLoop (parameters.map some)
  let mut obligations := []
  let context ← Simp.mkContext
    (config := { iota := false, zeta := false, zetaDelta := false })
  for tag in #[`equation, `initial, `next_state, `decreases, `input_size, `check_peak,
      `step_peak, `stop_peak, `step_time, `check_time, `stop_time, `step_pos, `stop_pos] do
    let type ← whnf (← inferType result)
    let (obligation, _) ← dsimp (← instantiateMVars type.bindingDomain!) context
    let h ← mkFreshExprSyntheticOpaqueMVar obligation (tag := tag)
    result := mkApp result h
    obligations := obligations ++ [h.mvarId!]
  goal.assign result
  setGoals rest
  return (#[], false, source, obligations)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop using $method:sourceMeasuredLoop $[using $scope:ident]?) => do
    let (_, _, _, obligations) ← proveMeasuredLoop method scope
    setGoals (obligations ++ (← getGoals))
  | `(tactic| model_fun_prop using $method:sourceMeasuredLoop $[using $scope:ident]?) =>
    modelFunProp (proveMeasuredLoop method scope)

end Complexity.TreeProgram.Source
