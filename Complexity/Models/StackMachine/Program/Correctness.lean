/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Program.Basic
public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Control.Program.Correctness

/-! # Resource bounds for native stack-program compilation -/

@[expose] public section

namespace Complexity.StackMachine.Program

open Std.WP
open Controller (History)

variable {κ Γ α : Type} {xs : Array Γ}

/-- Compiling the control graph preserves the action count and final storage. -/
theorem run_compile {p : StackMachine.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : Cfg κ Γ Unit xs} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result observe apply q s n a t) :
    ∃ e, p.result e = a ∧
      (compile p).runFrom (s.mapState (fun _ ↦ q)) n =
        t.mapState (fun _ ↦ Sum.inr e) := by
  induction h with
  | done e s => exact ⟨e, rfl, rfl⟩
  | step q s h ih => exact ih

/-- Preserve the complete action history while interpreting a stack program. -/
@[simps -fullyApplied eval observe act]
def historySemantics (xs : Array Γ) :
    Program.Semantics (Option Γ × (κ → Option Γ)) (Action κ Γ Unit) (Op κ Γ) Op.Result
      (History (Cfg κ Γ Unit xs) (Action κ Γ Unit)) where
  eval := eval
  observe := observe
  act := apply

private theorem run_space_le [Fintype κ]
    {Q E : Type} {p : Program.Control (Option Γ × (κ → Option Γ)) (Action κ Γ Unit) Q E}
    {out : E → α} {q : Q ⊕ E} {s t : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)}
    {n : ℕ} {a : α}
    (h : p.Run out (historySemantics xs).observe (historySemantics xs).act q s n a t) :
    t.configSup Cfg.mass ≤ s.configSup Cfg.mass ⊔ (s.last.mass + Fintype.card κ * n) := by
  induction h with
  | done e s => exact le_sup_left
  | step q s h ih =>
    have hm := s.last.mass_apply_le (p.next q (observe s)).1
    simp only [historySemantics_act, historySemantics_observe, History.apply_def,
      History.configSup_snoc, History.last_snoc] at ih
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- A macro's time bound also bounds its temporary space, without inspecting its internals.
Reserved credits survive, so this rule composes with amortized time arguments. -/
theorem spec_history [Fintype κ] {p : StackMachine.Program κ Γ α}
    {c : Cfg κ Γ Unit xs} {n r S : ℕ} {P : α → Cfg κ Γ Unit xs → Prop}
    (h : Triple (p.verify (semantics xs)) (fun s b ↦ s = c ∧ n ≤ b)
      (fun a s b ↦ P a s ∧ r ≤ b) ())
    (hs : c.mass + Fintype.card κ * n ≤ S) (q : ℕ) :
    Triple (p.verify (historySemantics xs))
      (fun s b ↦ s.last = c ∧ s.configSup Cfg.mass ≤ S ∧ n + q ≤ b)
      (fun a s b ↦ P a s.last ∧ s.configSup Cfg.mass ≤ S ∧ r + q ≤ b) () := by
  obtain ⟨m, a, d, hm, he, hd, hr⟩ := Program.exec_of_spec h ⟨rfl, le_rfl⟩
  constructor
  rintro s b ⟨hc, hS, hb⟩
  obtain ⟨t, ht, hx⟩ := Program.Exec.lift (e := semantics xs) (e' := historySemantics xs)
    History.last (fun _ ↦ rfl)
    (fun _ _ ↦ History.last_snoc _ _) he s hc
  refine ⟨m, a, t, by omega, hx, ht ▸ hd, ?_, by omega⟩
  apply (run_space_le hx.toControl).trans
  exact sup_le hS (by rw [hc]; exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _).trans hs)

/-- Compiling preserves the endpoint and peak total stack length. -/
theorem run_compile_history [Fintype κ]
    {p : StackMachine.Program κ Γ α} {q : p.State ⊕ p.Exit}
    {s t : History (Cfg κ Γ Unit xs) (Action κ Γ Unit)} {n : ℕ} {a : α}
    (h : Program.Control.Run (p.toControl eval) p.result
      (historySemantics xs).observe (historySemantics xs).act q s n a t)
    (u : History (Cfg κ Γ (p.State ⊕ p.Exit) xs) (Action κ Γ (p.State ⊕ p.Exit)))
    (hc : u.last = s.last.mapState (fun _ ↦ q))
    (hs : u.configSup Cfg.mass = s.configSup Cfg.mass) :
    ∃ e, p.result e = a ∧
      (p.compile.runFrom u n).last = t.last.mapState (fun _ ↦ Sum.inr e) ∧
      (p.compile.runFrom u n).configSup Cfg.mass = t.configSup Cfg.mass := by
  induction h generalizing u with
  | done e s => exact ⟨e, rfl, hc, hs⟩
  | step q s h ih =>
    have hstep : p.compile.step u =
        let next := (p.toControl eval).next q (observe s)
        u.snoc (next.1.mapState (fun _ ↦ next.2)) := by
      have ho : (observe u : Option Γ × (κ → Option Γ)) = observe s := by
        simp [History.observe_def, observe_def, hc]
      rw [Controller.step_eq, History.state_def, state_def, hc, ho]
      rfl
    apply ih (p.compile.step u)
    · ext i <;> simp [hstep, hc]
    · simp [hstep, hc, hs, Cfg.mass]

/-- A history specification supplies independent time and peak-space bounds. -/
theorem computesInTimeAndSpace_history [Fintype κ] {p : StackMachine.Program κ Γ α}
    {xs ys : List Γ} {t s : ℕ}
    (h : Triple (p.verify (historySemantics xs.toArray))
      (fun h b ↦ h = History.nil ((execution xs).init ()) ∧ t ≤ b)
      (fun _ h _ ↦ h.last.output = ys.toArray ∧ h.configSup Cfg.mass ≤ s) ()) :
    p.compile.ComputesInTimeAndSpace xs ys t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Program.exec_of_spec h ⟨rfl, le_rfl⟩
  obtain ⟨e, _, hc, hv⟩ := run_compile_history he.toControl
    (History.nil (p.compile.initInput (Config := Cfg κ Γ _ xs.toArray) xs)) rfl
    (by simp [Cfg.mass, Controller.initInput])
  simp only [Controller.runFrom_nil, Controller.last_runHistoryFrom] at hc hv
  refine ⟨n, ?_, ?_, (p.compile.runHistory_spec _ _ n).length_le.trans hn, hv.le.trans hs⟩
  · exact (congrArg (fun c ↦ p.compile.halt c.state) hc).trans rfl
  · exact (congrArg Cfg.output hc).trans ho

/-- A total stack-program specification yields native computation and resource bounds. -/
theorem computesInTimeAndSpace [Fintype κ] (p : StackMachine.Program κ Γ α)
    {xs ys : List Γ} {t : ℕ}
    (h : Triple (p.verify (semantics xs.toArray))
      (fun c b ↦ c = (execution xs).init () ∧ t ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray) ()) :
    (compile p).ComputesInTimeAndSpace xs ys t (Fintype.card κ * t) := by
  apply computesInTimeAndSpace_history
  have hh := spec_history (n := t) (r := 0) (P := fun _ c ↦ c.output = ys.toArray)
    (by simpa using h) (S := Fintype.card κ * t) (by simp [Cfg.mass]) 0
  constructor
  rintro s b ⟨rfl, hb⟩
  simpa using hh.le_wp _ b ⟨rfl, by simp [Cfg.mass], by simpa using hb⟩

end Complexity.StackMachine.Program
