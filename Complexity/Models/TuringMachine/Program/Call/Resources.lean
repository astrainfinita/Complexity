/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Call
public import Complexity.Control.Transition.Simulation

/-! # Calling a machine with its complete visit history

Calls preserve the source execution on tracked configurations, including earlier visits.
Space bounds follow from the exact final configuration in the call specification.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {κ : Type} {Γ Q : Type} [FinEnum Q] [Inhabited Γ] {xs : Array Γ}

/-- Compiling a call only relabels the source control state. -/
theorem step_callFrom (M : TM Id κ Γ Q) (q : Q) (c : TrackedCfg κ Γ Q xs) :
    (compile (callFrom M q)).step
      (Config := TrackedCfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
      (c.mapState (callRoute M)) =
      (M.step c).mapState (callRoute M) := by
  have hn (r : Q) (a : Γ) (v : κ → Γ) :
      ((callFrom M q).toControl eval).next (.inl (FinEnum.equiv r))
        (a, v) = let w := (M.transition r (a, v)).run
          (w.mapState (fun _ ↦ ()), callRoute M w.state) := by
    simp only [callFrom, Program.callControl, Program.pure,
      Program.ret, Program.Syntax.toControl,
      callBlock, Equiv.symm_apply_apply]
    cases hh : M.halt ((M.transition r (a, v)).run).state <;>
      simp only [blockRoute, callRoute, hh, Bool.false_eq_true, ↓reduceIte,
        Program.Syntax.callLabel, Program.Syntax.callCont] <;> rfl
  simp only [Controller.step_eq, TrackedCfg.state_def, Cfg.state_def]
  erw [halt_callRoute]
  split_ifs with h
  · rfl
  · have hf : M.halt c.cfg.state = false := Bool.eq_false_iff.mpr h
    have ht : ((compile (callFrom M q)).transition (callRoute M c.cfg.state)
        (c.cfg.inputSymbol, c.cfg.workSymbols)).run =
        ((M.transition c.cfg.state (c.cfg.inputSymbol, c.cfg.workSymbols)).run).mapState
          (callRoute M) := by
      simp only [callRoute, hf, Bool.false_eq_true, ↓reduceIte]
      change (let r := (((callFrom M q).toControl eval).next
          (.inl (FinEnum.equiv c.cfg.state)) (c.cfg.inputSymbol, c.cfg.workSymbols))
        r.1.mapState (fun _ ↦ r.2)) = _
      rw [hn]
      rfl
    erw [ht]
    exact TrackedCfg.apply_mapState _ _ _

/-- Calls have exactly the source machine's configurations, including halted padding. -/
theorem runFrom_callFrom (M : TM Id κ Γ Q) (q : Q) (c : TrackedCfg κ Γ Q xs)
    (n : ℕ) :
    (compile (callFrom M q)).runFrom
      (Config := TrackedCfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
      (c.mapState (callRoute M)) n =
      (M.runFrom c n).mapState (callRoute M) := by
  exact Transition.runN_map (fun c ↦ c.mapState (callRoute M)) (step_callFrom M q) c n

/-- Running a compiled call from fresh tapes reproduces the selected source execution. -/
theorem run_callFrom (M : TM Id κ Γ Q) (q : Q) (xs : List Γ) (n : ℕ) :
    (compile (callFrom M q)).run
      (TrackedCfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs.toArray) xs n =
      (M.runFrom ((rawExecution (κ := κ) xs).init q).track n).mapState (callRoute M) := by
  rw [Controller.run, initInput_tracked, initInput_raw, start_callFrom]
  exact runFrom_callFrom M q ((rawExecution (κ := κ) xs).init q).track n

/-- A call preserves a common interval bound containing its actual source execution.
The caller's existing visitation history and remaining time credits are retained. -/
@[spec]
theorem spec_callFrom_visited_le (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (V : κ → NonemptyInterval ℤ) (hh : M.Halted (M.runFrom c n))
    (hw : (M.runFrom c.track n).visited ≤ V) :
    Triple ((callFrom M c.state).verify (semantics xs))
      (fun s b ↦ s.cfg = c.mapState (fun _ ↦ ()) ∧ s.visited ≤ V ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.cfg = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.visited ≤ V ∧ r ≤ b) () := by
  constructor
  rintro s b ⟨hc, hv, hb⟩
  let u := s.mapState (fun _ ↦ c.state)
  have hu : u.cfg = c := by
    simp only [u, TrackedCfg.mapState_cfg, hc, Cfg.mapState_mapState]
    rfl
  apply (spec_callFrom M u n r (by simpa [hu] using hh)).entails_wp_of_post
    ?_ s b ⟨rfl, hb⟩
  rintro a t b' ⟨ha, rfl, hr⟩
  refine ⟨by simpa [hu] using ha, by simp [hu], ?_, hr⟩
  rw [TrackedCfg.mapState_visited, tracked_runFrom_visited_sup]
  exact sup_le hv (by simpa [hu] using hw)

/-- The initial-state call uses the same interval rule without resetting caller storage. -/
@[spec]
theorem spec_call_visited_le (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (V : κ → NonemptyInterval ℤ) (hc : c.state = M.q₀)
    (hh : M.Halted (M.runFrom c n))
    (hw : (M.runFrom c.track n).visited ≤ V) :
    Triple ((call M).verify (semantics xs))
      (fun s b ↦ s.cfg = c.mapState (fun _ ↦ ()) ∧ s.visited ≤ V ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.cfg = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.visited ≤ V ∧ r ≤ b) () := by
  simpa only [call, hc] using spec_callFrom_visited_le M c n r V hh hw

end Complexity.TM.Program
