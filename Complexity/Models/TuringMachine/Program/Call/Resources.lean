/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Call
public import Complexity.Models.TuringMachine.Program.Specification.Trace
public import Complexity.Control.Transition.Simulation

/-! # Calling a machine inside a shared work-space bound

A call visits precisely the work cells of the source machine. Its interval specification
therefore preserves caller-chosen bounds containing both earlier visits and the called run.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {κ : Type} {Γ Q : Type} [FinEnum Q] [Inhabited Γ] {xs : Array Γ}

/-- Compiling a call only relabels the source control state. -/
theorem step_callFrom (M : TM Id κ Γ Q) (q : Q) (c : Cfg κ Γ Q xs) :
    (compile (callFrom M q)).step
      (Config := Cfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
      (c.mapState (callRoute M)) =
      (M.step c).mapState (callRoute M) := by
  have hn (r : Q) (a : Γ) (v : κ → Γ) :
      (Complexity.Program.compile eval (callFrom M q)).next (.inl (FinEnum.equiv r))
        (a, v) = let w := (M.transition r (a, v)).run
          (w.mapState (fun _ ↦ ()), callRoute M w.state) := by
    simp only [callFrom, Complexity.Program.call, Complexity.Program.pure,
      Complexity.Program.ret, Complexity.Program.compile, Complexity.Program.Syntax.compile,
      callBlock, Equiv.symm_apply_apply]
    cases hh : M.halt ((M.transition r (a, v)).run).state <;>
      simp only [blockRoute, callRoute, hh, Bool.false_eq_true, ↓reduceIte,
        Complexity.Program.Syntax.callLabel, Complexity.Program.Syntax.callCont] <;> rfl
  simp only [TM.step_eq]
  erw [halt_callRoute]
  split_ifs with h
  · rfl
  · have hf : M.halt c.state = false := Bool.eq_false_iff.mpr h
    have ht : ((compile (callFrom M q)).transition (callRoute M c.state)
        (c.inputSymbol, c.workSymbols)).run =
        ((M.transition c.state (c.inputSymbol, c.workSymbols)).run).mapState (callRoute M) := by
      simp only [callRoute, hf, Bool.false_eq_true, ↓reduceIte]
      change (let r := ((Complexity.Program.compile eval (callFrom M q)).next
          (.inl (FinEnum.equiv c.state)) (c.inputSymbol, c.workSymbols))
        r.1.mapState (fun _ ↦ r.2)) = _
      rw [hn]
      rfl
    erw [ht]
    exact Action.apply_mapState _ _ _

/-- Calls have exactly the source machine's configurations, including halted padding. -/
theorem runFrom_callFrom (M : TM Id κ Γ Q) (q : Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) :
    (compile (callFrom M q)).runFrom
      (Config := Cfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs)
      (c.mapState (callRoute M)) n =
      (M.runFrom c n).mapState (callRoute M) := by
  exact Transition.runN_map (fun c ↦ c.mapState (callRoute M)) (step_callFrom M q) c n

/-- Running a compiled call from fresh tapes reproduces the selected source execution. -/
theorem run_callFrom (M : TM Id κ Γ Q) (q : Q) (xs : List Γ) (n : ℕ) :
    (compile (callFrom M q)).run
      (Config := Cfg κ Γ ((callFrom M q).State ⊕ (callFrom M q).Exit) xs.toArray) xs n =
      (M.runFrom ((rawExecution (κ := κ) xs).init q) n).mapState (callRoute M) := by
  rw [Controller.run, initInput_raw, start_callFrom]
  exact runFrom_callFrom M q ((rawExecution (κ := κ) xs).init q) n

/-- The call introduces no additional work-head visits. -/
theorem visited_callFrom (M : TM Id κ Γ Q) (q : Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) (i : κ) :
    (compile (callFrom M q)).visited (c.mapState (callRoute M)) n i =
      M.visited c n i := by
  simp only [TM.visited, runFrom_callFrom, Cfg.mapState_workPos]

/-- A call preserves a common interval bound containing its actual source execution.
The caller's existing visitation history and remaining time credits are retained. -/
@[spec]
theorem spec_callFrom_within (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (L R : κ → ℤ) (hh : M.Halted (M.runFrom c n))
    (hw : ∀ i, M.visited c n i ⊆ Finset.Icc (L i) (R i)) :
    Triple ((callFrom M c.state).verify (semantics xs))
      (fun s b ↦ s.cfg = c.mapState (fun _ ↦ ()) ∧ s.Within L R ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.cfg = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.Within L R ∧ r ≤ b) () := by
  constructor
  rintro s b ⟨hc, hs, hb⟩
  obtain ⟨m, hm, hr⟩ := exec_callFrom M c n hh
  obtain ⟨t, ht, he⟩ := Complexity.Program.Exec.lift TrackedCfg.cfg
    (e := cfgSemantics xs) (e' := semantics xs)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) hr s hc
  obtain ⟨e, _, he'⟩ := run_compile (Complexity.Program.Exec.compile he)
  have h₀ : s.cfg.mapState (fun _ ↦
      (Complexity.Program.compile eval (callFrom M c.state)).start) =
      c.mapState (callRoute M) := by
    change s.cfg.mapState (fun _ ↦ (compile (callFrom M c.state)).q₀) = _
    rw [start_callFrom, hc]
    rfl
  have hF := (compile (callFrom M c.state)).tracked_runFrom_within
    (s.mapState (fun _ ↦ (Complexity.Program.compile eval (callFrom M c.state)).start))
    m hs (fun i ↦ by
      erw [TrackedCfg.mapState_cfg, h₀, visited_callFrom]
      exact (M.visited_mono c hm i).trans (hw i))
  erw [he', TrackedCfg.within_mapState] at hF
  exact ⟨m, (M.runFrom c n).state, t, by omega, he,
    rfl, ht, hF, by omega⟩

/-- The initial-state call uses the same interval rule without resetting caller storage. -/
@[spec]
theorem spec_call_within (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (L R : κ → ℤ) (hc : c.state = M.q₀)
    (hh : M.Halted (M.runFrom c n))
    (hw : ∀ i, M.visited c n i ⊆ Finset.Icc (L i) (R i)) :
    Triple ((call M).verify (semantics xs))
      (fun s b ↦ s.cfg = c.mapState (fun _ ↦ ()) ∧ s.Within L R ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s.cfg = (M.runFrom c n).mapState (fun _ ↦ ()) ∧
        s.Within L R ∧ r ≤ b) () := by
  simpa only [call, hc] using spec_callFrom_within M c n r L R hh hw

end Complexity.TM.Program
