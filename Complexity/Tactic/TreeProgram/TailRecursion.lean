/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Primitives

/-! # Source-guided tail loops

Callbacks are selected once. Remaining time pays for the next round or the final result;
space bounds every reachable state relative to the initial input, without a saved-call stack.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

/-- Source equations discharge the loop's functional invariant. Time itself proves termination. -/
theorem Implements.tail_loop {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
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

namespace HasProgram

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {test : α → Bool} {next : α → α} {finish result : α → β} {tc pc ts ps td pd : α → ℕ}
  {qc qs qd : Value → Code Value}

/-- A tail loop of selected callbacks. A remaining-work potential pays for the rounds, so round
costs may vary between states; one coefficient covers every reachable state of every initial
input. The terminal callback is paid once, and space is a peak over the run. -/
theorem tail_loop_potential (hc : HasProgram test qc tc pc) (hs : HasProgram next qs ts ps)
    (hd : HasProgram finish qd td pd)
    (I : α → α → Prop) (potential : α → α → ℕ) (stop peak : α → ℕ)
    (equation : ∀ y, result y = if test y then result (next y) else finish y)
    (initial : ∀ x, I x x)
    (next_state : ∀ x y, I x y → test y = true → I x (next y))
    (input_size : Dominated (fun z : {p : α × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (check_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => pc z.1.2) (fun z => peak z.1.1))
    (step_peak : Dominated (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = true} => ps z.1.2)
      (fun z => peak z.1.1))
    (stop_peak : Dominated (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = false} => pd z.1.2)
      (fun z => peak z.1.1))
    (stop_time : Dominated
      (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = false} => td z.1.2 + 1)
      (fun z => stop z.1.1))
    (round_time : Dominated
      (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = true} => ts z.1.2 + tc (next z.1.2) + 1)
      (fun z => potential z.1.1 z.1.2 - potential z.1.1 (next z.1.2))) :
    HasProgram result (loopCode qc qs qd) (fun x => tc x + (potential x x + stop x) + 1) peak := by
  obtain ⟨bc, hbc, hct, hcp⟩ := hc.sound
  obtain ⟨bs, hbs, hst, hsp⟩ := hs.sound
  obtain ⟨bd, hbd, hdt, hdp⟩ := hd.sound
  let Z := {p : α × α // I p.1 p.2}
  have local_peak : Dominated (fun z : Z => max (bc.peak z.1.2)
      (if test z.1.2 then bs.peak z.1.2 else bd.peak z.1.2)) (fun z => peak z.1.1) := by
    have hc := (hcp.comp (fun z : Z => z.1.2)).trans check_peak
    apply Dominated.of_cases (fun z : Z => test z.1.2 = true)
    · let u (z : {z : Z // test z.1.2 = true}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = true} := ⟨z.1.1, z.1.2, z.2⟩
      have hs := (hsp.comp (fun z => (u z).1.2)).trans (step_peak.comp u)
      apply ((hc.comp Subtype.val).max_same hs).mono_left
      intro z
      simp only [Function.comp_apply, z.2, ↓reduceIte, u]
      exact le_rfl
    · let u (z : {z : Z // ¬test z.1.2 = true}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = false} := ⟨z.1.1, z.1.2, by simpa using z.2⟩
      have hd := (hdp.comp (fun z => (u z).1.2)).trans (stop_peak.comp u)
      apply ((hc.comp Subtype.val).max_same hd).mono_left
      intro z
      simp only [Function.comp_apply, z.2, Bool.false_eq_true, ↓reduceIte, u]
      exact le_rfl
  have stop_exact : Dominated (fun z : Z => if test z.1.2 then 0 else bd.time z.1.2 + 2)
      (fun z => stop z.1.1) := by
    apply Dominated.of_cases (fun z : Z => test z.1.2 = false)
    · let f (z : {z : Z // test z.1.2 = false}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = false} := ⟨z.1.1, z.1.2, z.2⟩
      have hd := (hdt.comp (fun z => (f z).1.2)).add (Dominated.const 2)
      apply (hd.trans (stop_time.comp f)).mono_left
      intro z
      simp only [Function.comp_def, f, z.2, Bool.false_eq_true, ↓reduceIte, le_refl]
    · apply Dominated.of_le
      intro z
      have ht : test z.1.1.2 = true := Bool.eq_true_of_not_eq_false z.2
      change (if test z.1.1.2 = true then 0 else _) ≤ _
      rw [ite_eq_left ht]
      exact Nat.zero_le _
  have round_exact : Dominated
      (fun z : Z => if test z.1.2 then bs.time z.1.2 + bc.time (next z.1.2) + 6 else 0)
      (fun z => potential z.1.1 z.1.2 - potential z.1.1 (next z.1.2)) := by
    apply Dominated.of_cases (fun z : Z => test z.1.2 = true)
    · let f (z : {z : Z // test z.1.2 = true}) :
          {p : α × α // I p.1 p.2 ∧ test p.2 = true} := ⟨z.1.1, z.1.2, z.2⟩
      have h := ((hst.comp (fun z => (f z).1.2)).add (hct.comp (fun z => next (f z).1.2))).add
        (Dominated.const 6)
      apply (h.trans (round_time.comp f)).mono_left
      intro z
      simp only [Function.comp_def, f, z.2, ↓reduceIte, le_refl]
    · apply Dominated.of_le
      intro z
      change (if test z.1.1.2 = true then _ else 0) ≤ _
      rw [ite_eq_right z.2]
      exact Nat.zero_le _
  obtain ⟨Cs, hsize⟩ := input_size
  obtain ⟨Cp, hpeak⟩ := local_peak
  obtain ⟨Ct, hstop⟩ := stop_exact
  obtain ⟨Cr, hround⟩ := round_exact
  simp only [Nat.nsmul_eq_mul] at hsize hpeak hstop hround
  let time (x y : α) := Cr * potential x y + Ct * stop x
  let space (x : α) := (Cs + Cp) * peak x
  refine ⟨⟨fun x => bc.time x + time x x + 4, space⟩, ?_, ?_, ?_⟩
  · apply hbc.tail_loop hbs hbd I time space equation initial
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
        next_state x y hi ht, ?_⟩
      have := add_mul_le_mul_of_le_mul_tsub (by omega) hr
      dsimp only [time]
      omega
  · exact (hct.add (((Dominated.refl (fun x => potential x x)).const_mul_left Cr).add
      ((Dominated.refl stop).const_mul_left Ct))).add (Dominated.const 4)
  · exact (Dominated.refl peak).const_mul_left (Cs + Cp)

/-- A decreasing measure with one round allowance: the potential is
`measure state * step initial`. -/
theorem tail_loop (hc : HasProgram test qc tc pc) (hs : HasProgram next qs ts ps)
    (hd : HasProgram finish qd td pd)
    (I : α → α → Prop) (measure step stop peak : α → ℕ)
    (equation : ∀ y, result y = if test y then result (next y) else finish y)
    (initial : ∀ x, I x x)
    (next_state : ∀ x y, I x y → test y = true → I x (next y))
    (decreases : ∀ x y, I x y → test y = true → measure (next y) < measure y)
    (input_size : Dominated (fun z : {p : α × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (check_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => pc z.1.2) (fun z => peak z.1.1))
    (step_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => ps z.1.2) (fun z => peak z.1.1))
    (stop_peak : Dominated (fun z : {p : α × α // I p.1 p.2} => pd z.1.2) (fun z => peak z.1.1))
    (step_time : Dominated (fun z : {p : α × α // I p.1 p.2} => ts z.1.2) (fun z => step z.1.1))
    (check_time : Dominated (fun z : {p : α × α // I p.1 p.2} => tc (next z.1.2))
      (fun z => step z.1.1))
    (stop_time : Dominated (fun z : {p : α × α // I p.1 p.2} => td z.1.2) (fun z => stop z.1.1))
    (step_pos : ∀ x, 0 < step x) (stop_pos : ∀ x, 0 < stop x) :
    HasProgram result (loopCode qc qs qd) (fun x => tc x + (measure x * step x + stop x) + 1)
      peak :=
  tail_loop_potential hc hs hd I (fun x y => measure y * step x) stop peak equation initial
    next_state input_size check_peak
    (step_peak.comp (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = true} => ⟨z.1, z.2.1⟩))
    (stop_peak.comp (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = false} => ⟨z.1, z.2.1⟩))
    ((stop_time.comp (fun z : {p : α × α // I p.1 p.2 ∧ test p.2 = false} => ⟨z.1, z.2.1⟩)).add_same
      (Dominated.const_of_pos 1 fun z => stop_pos z.1.1))
    (by
      let u (z : {p : α × α // I p.1 p.2 ∧ test p.2 = true}) : {p : α × α // I p.1 p.2} :=
        ⟨z.1, z.2.1⟩
      apply (((step_time.comp u).add_same (check_time.comp u)).add_same
        (Dominated.const_of_pos 1 fun z => step_pos z.1.1)).mono
      intro z
      change step z.1.1 ≤ measure z.1.2 * step z.1.1 - measure (next z.1.2) * step z.1.1
      rw [← Nat.sub_mul]
      have := decreases z.1.1 z.1.2 z.2.1 z.2.2
      exact Nat.le_mul_of_pos_left _ (by omega))

end HasProgram

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
    TacticM (List MVarId) := withSourceSpecs scope <| withMainContext do
  let `(sourceMeasuredLoop| loop (test := $test) (next := $next) (finish := $finish)
    (invariant := $inv) (measure := $measure) (step := $step) (stop := $stop) (space := $peak)) :=
    method | throwUnsupportedSyntax
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let args := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs
  let source := args[4]!
  let domain := args[0]!
  let test ← elabSourceTerm test (← mkArrow domain (mkConst ``Bool))
  let next ← elabSourceTerm next (← mkArrow domain domain)
  let finish ← elabSourceTerm finish (← inferType source)
  let inv ← elabSourceTerm inv (← mkArrow domain (← mkArrow domain (mkSort .zero)))
  let budgetType ← mkArrow domain (mkConst ``Nat)
  let measure ← elabSourceTerm measure budgetType
  let step ← elabSourceTerm step budgetType
  let stop ← elabSourceTerm stop budgetType
  let peak ← elabSourceTerm peak budgetType
  Term.synthesizeSyntheticMVarsNoPostponing
  let session ← Search.Session.create
  let mut callbacks := #[]
  let mut growth := #[]
  for (name, callback) in #[(`test, test), (`next, next), (`finish, finish)] do
    let impl ← certifyCallback session `loop name callback
    let type := (← whnfR (← inferType impl)).getAppArgs
    unless type.size == 8 do
      throwError "source loop: unexpected callback program type {← inferType impl}"
    callbacks := callbacks.push impl
    growth := growth.push type[6]! |>.push type[7]!
  -- The loop's output type is that of `finish`, fixed by unification.
  let parameters := #[some args[0]!, none, some args[2]!, none] ++
    ((#[test, next, finish, source] ++ growth).map some) ++ #[none, none, none] ++
    ((callbacks ++ #[inv, measure, step, stop, peak]).map some)
  let mut result ← mkAppOptM ``HasProgram.tail_loop parameters
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
  let comparisons ← finishProgram goal result
  setGoals rest
  return obligations ++ comparisons

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop using $method:sourceMeasuredLoop $[using $scope:ident]?) => do
    let obligations ← proveMeasuredLoop method scope
    setGoals (obligations ++ (← getGoals))
  | `(tactic| model_fun_prop using $method:sourceMeasuredLoop $[using $scope:ident]?) =>
    modelFunProp (proveMeasuredLoop method scope)

end Complexity.TreeProgram.Source
