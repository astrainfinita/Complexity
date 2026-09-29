/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Call
public import Complexity.Control.Transition.Simulation

/-! # Calling a machine with its complete visit history

Calls preserve the source execution history, including earlier visits.
Space bounds follow from the exact final configuration in the call specification.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP
open Controller (History)

variable {κ : Type} {Γ Q : Type} [FinEnum Q] [Inhabited Γ] {xs : Array Γ}

/-- Compiling a call only relabels the source control state. -/
theorem step_callFrom (M : TM Id κ Γ Q) (q : Q) (c : History (Cfg κ Γ Q xs) (Action κ Γ Q)) :
    (compile (callFrom M q)).step
      (Config := History (Cfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
        (Action κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit)))
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
  simp only [Controller.step_eq, History.state_def, Cfg.state_def]
  erw [History.last_mapState, History.observe_mapState, halt_callRoute]
  split_ifs with h
  · rfl
  · have hf : M.halt c.last.state = false := Bool.eq_false_iff.mpr h
    have ht : ((compile (callFrom M q)).transition (callRoute M c.last.state)
        (c.last.inputSymbol, c.last.workSymbols)).run =
        ((M.transition c.last.state (c.last.inputSymbol, c.last.workSymbols)).run).mapState
          (callRoute M) := by
      simp only [callRoute, hf, Bool.false_eq_true, ↓reduceIte]
      change (let r := (((callFrom M q).toControl eval).next
          (.inl (FinEnum.equiv c.last.state)) (c.last.inputSymbol, c.last.workSymbols))
        r.1.mapState (fun _ ↦ r.2)) = _
      rw [hn]
      rfl
    erw [ht]
    exact History.apply_mapState _ _ _

/-- Calls have exactly the source machine's configurations, including halted padding. -/
theorem runFrom_callFrom (M : TM Id κ Γ Q) (q : Q) (c : History (Cfg κ Γ Q xs) (Action κ Γ Q))
    (n : ℕ) :
    (compile (callFrom M q)).runFrom
      (Config := History (Cfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
        (Action κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit)))
      (c.mapState (callRoute M)) n =
      (M.runFrom c n).mapState (callRoute M) := by
  exact Transition.runN_map (fun c ↦ c.mapState (callRoute M)) (step_callFrom M q) c n

/-- A call preserves a common interval bound containing its actual source execution.
The caller's existing visitation history and remaining time credits are retained. -/
@[spec]
theorem spec_callFrom_visited_le (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (V : κ → NonemptyInterval ℤ) (hh : M.Halted (M.runFrom c n))
    (hw : (M.runHistoryFrom c n).visited ≤ V) :
    Triple ((callFrom M c.state).verify (semantics xs))
      (fun s b ↦ s.last = c.mapState (fun _ ↦ ()) ∧ s.visited ≤ V ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.last = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.visited ≤ V ∧ r ≤ b) () := by
  constructor
  rintro s b ⟨hc, hv, hb⟩
  let u := s.mapState (fun _ ↦ c.state)
  have hu : u.last = c := by
    simp only [u, History.last_mapState, hc, Cfg.mapState_mapState]
    rfl
  rw [← hu] at hh hw ⊢
  apply (spec_callFrom M u n r (by simpa using hh)).entails_wp_of_post
    ?_ s b ⟨by
      simp only [u, History.mapState_mapState]
      exact (History.mapState_id s).symm, hb⟩
  rintro a t b' ⟨ha, rfl, hr⟩
  refine ⟨by simpa using ha, by simp, ?_, hr⟩
  rw [History.visited_mapState, Controller.runFrom_history, History.visited_append]
  exact sup_le (by simpa [u] using hv) hw

/-- The initial-state call uses the same interval rule without resetting caller storage. -/
@[spec]
theorem spec_call_visited_le (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (V : κ → NonemptyInterval ℤ) (hc : c.state = M.q₀)
    (hh : M.Halted (M.runFrom c n))
    (hw : (M.runHistoryFrom c n).visited ≤ V) :
    Triple ((call M).verify (semantics xs))
      (fun s b ↦ s.last = c.mapState (fun _ ↦ ()) ∧ s.visited ≤ V ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.last = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.visited ≤ V ∧ r ≤ b) () := by
  simpa only [call, hc] using spec_callFrom_visited_le M c n r V hh hw

end Complexity.TM.Program
