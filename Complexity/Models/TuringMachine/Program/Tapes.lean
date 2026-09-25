/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.Configuration
public import Complexity.Models.TuringMachine.Program.Enumeration
public import Complexity.Models.TuringMachine.Tapes
public import Complexity.Control.Program.Correctness

/-! # Calling a program on selected work tapes

Only observations and actions change at the call boundary. The existing compiler and call
constructor preserve the result and exact transition count; tapes outside the layout stay
untouched. Input and output remain shared with the caller.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {κ τ : Type} [Fintype κ] [DecidableEq τ] {Γ α : Type}

/-- Adapt a compiled controller's observations and actions to a work layout. -/
def workControl (L : κ ↪ τ) (p : Program κ Γ α) :
    Complexity.Program.Control (Γ × (τ → Γ)) (Action τ Γ Unit)
      (Fin (FinEnum.card p.State)) (Fin (FinEnum.card p.Exit)) where
  start := Sum.map FinEnum.equiv FinEnum.equiv (Complexity.Program.compile eval p).start
  next q v :=
    let (a, q') := (Complexity.Program.compile eval p).next (FinEnum.equiv.symm q)
      (v.1, v.2 ∘ L)
    (a.liftWorkAlong L, Sum.map FinEnum.equiv FinEnum.equiv q')

/-- Run a local program on selected work tapes, sharing input and output with its caller.
The return type is unchanged and the call adds no transitions. -/
def onWork (L : κ ↪ τ) (p : Program κ Γ α) : Program τ Γ α :=
  Complexity.Program.call (workControl L p)
    (fun e ↦ pure (p.result (FinEnum.equiv.symm e)))

variable [Inhabited Γ] {xs : Array Γ}

private theorem run_workControl (L : κ ↪ τ) (p : Program κ Γ α)
    (c : Cfg τ Γ Unit xs) {q : p.State ⊕ p.Exit} {s t : Cfg κ Γ Unit xs}
    {n : ℕ} {a : α}
    (h : Complexity.Program.Control.Run (Complexity.Program.compile eval p) p.result
      (cfgSemantics xs).observe (cfgSemantics xs).act q s n a t) :
    ∃ e : p.Exit, p.result e = a ∧
      Complexity.Program.Control.Run (workControl L p) id
        (cfgSemantics xs).observe (cfgSemantics xs).act
        (Sum.map FinEnum.equiv FinEnum.equiv q) (Cfg.replaceWorkAlong L s c) n
        (FinEnum.equiv e) (Cfg.replaceWorkAlong L t c) := by
  induction h with
  | done e s => exact ⟨e, rfl, .done _ _⟩
  | step q s h ih =>
    obtain ⟨e, he, hr⟩ := ih
    have ho : ((Cfg.replaceWorkAlong L s c).inputSymbol,
        (Cfg.replaceWorkAlong L s c).workSymbols ∘ L) =
        (s.inputSymbol, s.workSymbols) := by
      congr 1
      funext i
      simp [Cfg.workSymbols]
    refine ⟨e, he, ?_⟩
    apply Complexity.Program.Control.Run.step
    simpa only [workControl, Equiv.symm_apply_apply, cfgSemantics, Cfg.observe_def, ho,
      Action.apply_liftWorkAlong_replaceWorkAlong] using hr

/-- Layout calls preserve the exact execution and install its local result in the caller. -/
theorem exec_onWork (L : κ ↪ τ) {p : Program κ Γ α}
    {c : Cfg τ Γ Unit xs} {t : Cfg κ Γ Unit xs} {n : ℕ} {a : α}
    (h : p.Exec (cfgSemantics xs) (c.restrictWorkAlong L) n a t) :
    (onWork L p).Exec (cfgSemantics xs) c n a (Cfg.replaceWorkAlong L t c) := by
  obtain ⟨e, he, hr⟩ := run_workControl L p c (Complexity.Program.Exec.compile h)
  have hh := Complexity.Program.Syntax.Exec.call (e := cfgSemantics xs)
    (workControl L p) (fun e ↦ Complexity.Program.Syntax.ret (u := .value)
      (p.result (FinEnum.equiv.symm e))) hr
    (Complexity.Program.Syntax.Exec.ret (v := .value) _ _)
  simpa only [onWork, Complexity.Program.call, Pure.pure, Complexity.Program.ret,
    Cfg.replaceWorkAlong_restrictWorkAlong, Nat.add_zero, Equiv.symm_apply_apply, he] using hh

/-- Reuse a local total specification while retaining every unselected tape and head.
The postcondition keeps arbitrary local assertions and the caller's exact remaining budget. -/
theorem spec_onWork (L : κ ↪ τ) {p : Program κ Γ α}
    {P : Cfg κ Γ Unit xs → ℕ → Prop} {Q : α → Cfg κ Γ Unit xs → ℕ → Prop}
    (h : Triple (p.verify (cfgSemantics xs)) P Q ()) (c : Cfg τ Γ Unit xs) :
    Triple ((onWork L p).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ P (c.restrictWorkAlong L) b)
      (fun a s b ↦ ∃ t, Q a t b ∧ s = Cfg.replaceWorkAlong L t c) () := by
  constructor
  rintro s b ⟨hs, hb⟩
  subst s
  obtain ⟨n, a, t, hn, hr, hq⟩ := h.le_wp (c.restrictWorkAlong L) b hb
  exact ⟨n, a, Cfg.replaceWorkAlong L t c, hn, exec_onWork L hr, t, hq, rfl⟩

end Complexity.TM.Program
