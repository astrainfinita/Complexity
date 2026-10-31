/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.History
public import Complexity.Models.TuringMachine.Program.Enumeration

/-! # Calling an existing finite Turing machine as a program

The source machine's states become program nodes and exits. Calling does not clear storage,
reset heads, or discard output. Every source transition is one program action, including the
transition entering a halting state; an already halted state returns without an action.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP
open Controller (History)

variable {κ : Type} {Γ Q : Type} [FinEnum Q]

/-- Halting source labels are block exits; other labels remain internal. -/
def blockRoute (M : TM Id κ Γ Q) (q : Q) :
    Fin (FinEnum.card Q) ⊕ Fin (FinEnum.card Q) :=
  if M.halt q then .inr (FinEnum.equiv q) else .inl (FinEnum.equiv q)

/-- Use the supplied state numbering without constructing a transition table. -/
def callBlock (M : TM Id κ Γ Q) (q : Q) :
    Program.Control (Γ × (κ → Γ)) (Action κ Γ)
      (Fin (FinEnum.card Q)) (Fin (FinEnum.card Q)) where
  start := blockRoute M q
  next q v :=
    let a := (M.transition (FinEnum.equiv.symm q) v).run
    (a.2, blockRoute M a.1)

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

private theorem run_callBlock (M : TM Id κ Γ Q) (q r : Q)
    (s : History (Cfg κ Γ xs) (Action κ Γ)) (n : ℕ) (hh : M.Halted (M.runFrom (r, s) n)) :
    ∃ m ≤ n, Program.Control.Run (callBlock M q) id
      (semantics xs).observe (semantics xs).act (blockRoute M r) s m
      (FinEnum.equiv (M.runFrom (r, s) n).1) (M.runFrom (r, s) n).2 := by
  induction n generalizing r s with
  | zero =>
    have hc : M.halt r = true := hh
    refine ⟨0, le_rfl, ?_⟩
    simp only [blockRoute, hc, ↓reduceIte, Controller.runFrom_zero]
    exact Program.Control.Run.done _ _
  | succ n ih =>
    by_cases hc : M.halt r
    · rw [M.runFrom_of_halted (r, s) hc (n + 1)]
      refine ⟨0, Nat.zero_le _, ?_⟩
      simp only [blockRoute, hc, ↓reduceIte]
      exact Program.Control.Run.done _ _
    · rw [Controller.runFrom_succ, M.step_of_not_halted (r, s) hc] at hh ⊢
      obtain ⟨m, hm, hr⟩ := ih _ _ hh
      refine ⟨m + 1, by omega, ?_⟩
      simp only [blockRoute, hc, Bool.false_eq_true, ↓reduceIte]
      exact Program.Control.Run.step _ _ (by simpa [callBlock] using hr)

/-- A bounded halting run gives an actual call execution of at most the same length. -/
theorem exec_callFrom (M : TM Id κ Γ Q) (q : Q) (s : History (Cfg κ Γ xs) (Action κ Γ))
    (n : ℕ) (hh : M.Halted (M.runFrom (q, s) n)) :
    ∃ m ≤ n, (callFrom M q).Exec (semantics xs) s m (M.runFrom (q, s) n).1
      (M.runFrom (q, s) n).2 := by
  obtain ⟨m, hm, hr⟩ := run_callBlock M q q s n hh
  refine ⟨m, hm, ?_⟩
  have h := Program.Syntax.Exec.call
    (callBlock M q) (fun e ↦
      Program.Syntax.ret
        ((FinEnum.equiv : Q ≃ Fin (FinEnum.card Q)).symm e))
    hr (Program.Syntax.Exec.ret (v := .value) _ _)
  simpa only [callFrom, Program.callControl, Program.pure,
    Program.ret, Nat.add_zero, Equiv.symm_apply_apply] using h

/-- A call runs the machine from the selected state on the current history and returns its
halting state; credits reserved for the continuation survive. -/
@[spec]
theorem spec_callFrom (M : TM Id κ Γ Q) (q : Q) (s : History (Cfg κ Γ xs) (Action κ Γ))
    (n r : ℕ) (hh : M.Halted (M.runFrom (q, s) n)) :
    Triple ((callFrom M q).verify (semantics xs))
      (fun s' b ↦ s' = s ∧ n + r ≤ b)
      (fun a s' b ↦ a = (M.runFrom (q, s) n).1 ∧ s' = (M.runFrom (q, s) n).2 ∧ r ≤ b) () := by
  constructor
  rintro s' b ⟨rfl, hb⟩
  obtain ⟨m, hm, hr⟩ := exec_callFrom M q s' n hh
  exact ⟨m, _, _, by omega, hr, rfl, rfl, by omega⟩

/-- Start at the machine's initial control state without resetting storage or visit history. -/
@[spec]
theorem spec_call (M : TM Id κ Γ Q) (s : History (Cfg κ Γ xs) (Action κ Γ))
    (n r : ℕ) (hh : M.Halted (M.runFrom (M.q₀, s) n)) :
    Triple ((call M).verify (semantics xs))
      (fun s' b ↦ s' = s ∧ n + r ≤ b)
      (fun a s' b ↦ a = (M.runFrom (M.q₀, s) n).1 ∧ s' = (M.runFrom (M.q₀, s) n).2 ∧ r ≤ b)
      () :=
  spec_callFrom M M.q₀ s n r hh

/-- A call preserves the complete final configuration and credits reserved for its continuation. -/
@[spec]
theorem cfg_spec_callFrom (M : TM Id κ Γ Q) (q : Q) (c : Cfg κ Γ xs)
    (n r : ℕ) (hh : M.Halted (M.runFrom (q, c) n)) :
    Triple ((callFrom M q).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom (q, c) n).1 ∧ s = (M.runFrom (q, c) n).2 ∧ r ≤ b) () := by
  apply cfg_of_history (spec_callFrom M q (History.nil c) n r
    (by simpa [Controller.Halted] using hh))
  · rintro s b ⟨rfl, hb⟩; exact ⟨rfl, hb⟩
  · rintro a s b ⟨ha, rfl, hb⟩
    simpa [History.last_snd] using And.intro ha hb

/-- Start at the machine's initial control state without resetting any storage or head. -/
@[spec]
theorem cfg_spec_call (M : TM Id κ Γ Q) (c : Cfg κ Γ xs)
    (n r : ℕ) (hh : M.Halted (M.runFrom (M.q₀, c) n)) :
    Triple ((call M).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ n + r ≤ b)
      (fun a s b ↦ a = (M.runFrom (M.q₀, c) n).1 ∧ s = (M.runFrom (M.q₀, c) n).2 ∧ r ≤ b)
      () :=
  cfg_spec_callFrom M M.q₀ c n r hh

end Complexity.TM.Program
