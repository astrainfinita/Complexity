/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.Tracked
public import Complexity.Models.TuringMachine.Program.Enumeration

/-! # Calling an existing finite Turing machine as a program

The source machine's states become program nodes and exits. Calling does not clear storage,
reset heads, or discard output. Every source transition is one program action, including the
transition entering a halting state; an already halted state returns without an action.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {κ : Type} {Γ Q : Type} [FinEnum Q]

/-- Halting source labels are block exits; other labels remain internal. -/
def blockRoute (M : TM Id κ Γ Q) (q : Q) :
    Fin (FinEnum.card Q) ⊕ Fin (FinEnum.card Q) :=
  if M.halt q then .inr (FinEnum.equiv q) else .inl (FinEnum.equiv q)

/-- Use the supplied state numbering without constructing a transition table. -/
def callBlock (M : TM Id κ Γ Q) (q : Q) :
    Program.Control (Γ × (κ → Γ)) (Action κ Γ Unit)
      (Fin (FinEnum.card Q)) (Fin (FinEnum.card Q)) where
  start := blockRoute M q
  next q v :=
    let a := (M.transition (FinEnum.equiv.symm q) v).run
    (a.mapState (fun _ ↦ ()), blockRoute M a.state)

/-- Call a machine from a selected finite control state and return its halting state.

The call uses the caller's current tapes and heads, without initialization or restoration.
`FinEnum` supplies the numbering needed by `Program.callControl`; the continuation converts
the numbered exit back to a state of the machine. Each source transition costs one step,
and an already halted entry returns without taking a step. -/
@[inline] def callFrom (M : TM Id κ Γ Q) (q : Q) : TM.Program κ Γ Q :=
  Program.callControl (callBlock M q) (fun e ↦ Program.pure (FinEnum.equiv.symm e))

/-- Call a machine from its initial control state and return its halting state.

This fixes the entry of `callFrom` to `M.q₀`; storage still comes from the caller's current
configuration. Unlike `Program.callControl`, it accepts a machine and supplies the exit
continuation itself. The call adds no transitions beyond the source machine's execution. -/
@[inline] def call (M : TM Id κ Γ Q) : TM.Program κ Γ Q := callFrom M M.q₀

/-- Embed a source label in the compiled call, including its pure return continuation. -/
def callRoute (M : TM Id κ Γ Q) (q : Q) :
    (callFrom M M.q₀).State ⊕ (callFrom M M.q₀).Exit :=
  if M.halt q then .inr ⟨FinEnum.equiv q, ⟨⟩⟩
  else .inl (.inl (FinEnum.equiv q))

/-- A compiled call starts at the imported source label. -/
@[simp] theorem start_callFrom (M : TM Id κ Γ Q) (q : Q) :
    (compile (callFrom M q)).q₀ = callRoute M q := by
  change ((callFrom M q).toControl eval).start = _
  simp only [callFrom, Program.callControl, Program.pure,
    Program.ret, Program.Syntax.toControl,
    callBlock]
  cases h : M.halt q <;>
    simp only [blockRoute, callRoute, h, Bool.false_eq_true, ↓reduceIte,
      Program.Syntax.callLabel, Program.Syntax.callCont] <;> rfl

/-- Importing a label preserves its halting status. -/
@[simp] theorem halt_callRoute (M : TM Id κ Γ Q) (q r : Q) :
    (compile (callFrom M q)).halt (callRoute M r) = M.halt r := by
  change Sum.elim (fun _ ↦ false) (fun _ ↦ true) (callRoute M r) = _
  cases h : M.halt r <;> simp only [callRoute, h, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- An already halted source state gives an immediately halted compiled call. -/
theorem halt_start_callFrom (M : TM Id κ Γ Q) (q : Q) :
    (compile (callFrom M q)).halt (compile (callFrom M q)).q₀ = M.halt q := by
  rw [start_callFrom, halt_callRoute]

variable [Inhabited Γ] {xs : Array Γ}

private theorem run_callBlock (M : TM Id κ Γ Q) (q : Q)
    (c : TrackedCfg κ Γ Q xs) (n : ℕ) (hh : M.Halted (M.runFrom c n)) :
    ∃ m ≤ n, Program.Control.Run (callBlock M q) id
      (semantics xs).observe (semantics xs).act (blockRoute M (state c))
      (c.mapState (fun _ ↦ ())) m (FinEnum.equiv (state (M.runFrom c n)))
      ((M.runFrom c n).mapState (fun _ ↦ ())) := by
  induction n generalizing c with
  | zero =>
    have hc : M.halt (state c) = true := hh
    refine ⟨0, le_rfl, ?_⟩
    simp only [blockRoute, hc, ↓reduceIte, Controller.runFrom_zero]
    exact Program.Control.Run.done _ _
  | succ n ih =>
    by_cases hc : M.Halted c
    · have hr := M.runFrom_of_halted c hc (n + 1)
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hr]
      have he : M.halt (state c) = true := hc
      simp only [blockRoute, he, ↓reduceIte]
      exact Program.Control.Run.done _ _
    · have hf : M.halt (state c) = false := Bool.eq_false_iff.mpr hc
      have hs := Controller.step_eq M c
      simp only [hf, Bool.false_eq_true, ite_false] at hs
      have hn : M.runFrom c (n + 1) = M.runFrom (M.step c) n := rfl
      obtain ⟨m, hm, hr⟩ := ih (M.step c) (hn ▸ hh)
      refine ⟨m + 1, by omega, ?_⟩
      simp only [hn, blockRoute, hf, Bool.false_eq_true, ↓reduceIte]
      apply Program.Control.Run.step
      simpa only [callBlock, Equiv.symm_apply_apply, semantics_observe, semantics_act,
        TrackedCfg.observe_def, TrackedCfg.mapState_cfg, Cfg.observe_def,
        Cfg.inputSymbol_mapState, Cfg.workSymbols_mapState, TrackedCfg.apply_mapState,
        hs, TrackedCfg.state_def, TrackedCfg.apply_cfg, Cfg.state_def, apply_state] using hr

/-- A bounded halting run gives an actual call execution of at most the same length. -/
theorem exec_callFrom (M : TM Id κ Γ Q) (c : TrackedCfg κ Γ Q xs)
    (n : ℕ) (hh : M.Halted (M.runFrom c n)) :
    ∃ m ≤ n, (callFrom M (state c)).Exec (semantics xs)
      (c.mapState (fun _ ↦ ())) m (state (M.runFrom c n))
      ((M.runFrom c n).mapState (fun _ ↦ ())) := by
  obtain ⟨m, hm, hr⟩ := run_callBlock M (state c) c n hh
  refine ⟨m, hm, ?_⟩
  have h := Program.Syntax.Exec.call (e := semantics xs)
    (callBlock M (state c)) (fun e ↦
      Program.Syntax.ret (α := Q) (u := .value)
        ((FinEnum.equiv : Q ≃ Fin (FinEnum.card Q)).symm e))
    hr (Program.Syntax.Exec.ret (v := .value) _ _)
  simpa only [callFrom, Program.callControl, Program.pure,
    Program.ret, Nat.add_zero, Equiv.symm_apply_apply] using h

/-- A call preserves the complete final configuration, including earlier visits and
credits reserved for its continuation. -/
@[spec]
theorem spec_callFrom (M : TM Id κ Γ Q) (c : TrackedCfg κ Γ Q xs)
    (n r : ℕ) (hh : M.Halted (M.runFrom c n)) :
    Triple ((callFrom M (state c)).verify (semantics xs))
      (fun s b ↦ s = c.mapState (fun _ ↦ ()) ∧ n + r ≤ b)
      (fun a s b ↦ a = state (M.runFrom c n) ∧
        s = (M.runFrom c n).mapState (fun _ ↦ ()) ∧ r ≤ b) () := by
  constructor
  rintro s b ⟨rfl, hb⟩
  obtain ⟨m, hm, hr⟩ := exec_callFrom M c n hh
  exact ⟨m, state (M.runFrom c n), (M.runFrom c n).mapState (fun _ ↦ ()),
    by omega, hr, rfl, rfl, by omega⟩

/-- Start at the machine's initial control state without resetting storage or visit history. -/
@[spec]
theorem spec_call (M : TM Id κ Γ Q) (c : TrackedCfg κ Γ Q xs)
    (n r : ℕ) (hc : state c = M.q₀) (hh : M.Halted (M.runFrom c n)) :
    Triple ((call M).verify (semantics xs))
      (fun s b ↦ s = c.mapState (fun _ ↦ ()) ∧ n + r ≤ b)
      (fun a s b ↦ a = state (M.runFrom c n) ∧
        s = (M.runFrom c n).mapState (fun _ ↦ ()) ∧ r ≤ b) () := by
  simpa only [call, hc] using spec_callFrom M c n r hh

/-- A call preserves the complete final configuration and credits reserved for its continuation. -/
@[spec]
theorem cfg_spec_callFrom (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (hh : M.Halted (M.runFrom c n)) :
    Triple ((callFrom M c.state).verify (cfgSemantics xs))
      (fun s b ↦ s = c.mapState (fun _ ↦ ()) ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s = (M.runFrom c n).mapState (fun _ ↦ ()) ∧ r ≤ b) () := by
  apply cfg_of_tracked (spec_callFrom M c.track n r (by simpa using hh))
  · rintro s b ⟨rfl, hb⟩; exact ⟨rfl, hb⟩
  · rintro a s b ⟨ha, rfl, hb⟩
    simpa using And.intro ha hb

/-- Start at the machine's initial control state without resetting any storage or head. -/
@[spec]
theorem cfg_spec_call (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n r : ℕ) (hc : c.state = M.q₀) (hh : M.Halted (M.runFrom c n)) :
    Triple ((call M).verify (cfgSemantics xs))
      (fun s b ↦ s = c.mapState (fun _ ↦ ()) ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom c n).state ∧
        s = (M.runFrom c n).mapState (fun _ ↦ ()) ∧ r ≤ b) () := by
  simpa only [call, hc] using cfg_spec_callFrom M c n r hh

end Complexity.TM.Program
