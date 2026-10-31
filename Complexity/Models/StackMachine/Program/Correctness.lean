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

/-- Preserve the complete action history while interpreting a stack program. -/
@[simps -fullyApplied eval observe act]
def historySemantics (xs : Array Γ) :
    Program.Semantics (Option Γ × (κ → Option Γ)) (Action κ Γ) (Op κ Γ) Op.Result
      (History (Cfg κ Γ xs) (Action κ Γ)) where
  eval := eval
  observe := observe
  act := apply

private theorem run_space_le [Fintype κ]
    {Q E : Type} {p : Program.Control (Option Γ × (κ → Option Γ)) (Action κ Γ) Q E}
    {out : E → α} {q : Q ⊕ E} {s t : History (Cfg κ Γ xs) (Action κ Γ)}
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
    {c : Cfg κ Γ xs} {n r S : ℕ} {P : α → Cfg κ Γ xs → Prop}
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

/-- A history specification supplies independent time and peak-space bounds. -/
theorem computesWithin_history [Fintype κ] {p : StackMachine.Program κ Γ α}
    {xs ys : List Γ} {t s : ℕ}
    (h : Triple (p.verify (historySemantics xs.toArray))
      (fun h b ↦ h = History.nil (Cfg.init κ xs) ∧ t ≤ b)
      (fun _ h _ ↦ h.last.output = ys.toArray ∧ h.configSup Cfg.mass ≤ s) ()) :
    p.compile.ComputesWithin xs ys t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Program.exec_of_spec h ⟨rfl, le_rfl⟩
  obtain ⟨e, _, hr⟩ := he.runFrom_compile idle
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact ⟨n, (congrArg p.compile.halt hr.1).trans rfl, (congrArg Cfg.output hl).trans ho,
    (History.length_snd _).trans_le ((p.compile.length_runHistory_le _ n).trans hn),
    (congrArg (·.configSup Cfg.mass) hr.2).le.trans hs⟩

/-- A total stack-program specification yields native computation and resource bounds. -/
theorem computesWithin [Fintype κ] (p : StackMachine.Program κ Γ α)
    {xs ys : List Γ} {t : ℕ}
    (h : Triple (p.verify (semantics xs.toArray))
      (fun c b ↦ c = Cfg.init κ xs ∧ t ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray) ()) :
    (compile p).ComputesWithin xs ys t (Fintype.card κ * t) := by
  apply computesWithin_history
  have hh := spec_history (r := 0)
    (by simpa using h) (S := Fintype.card κ * t) (by simp [Cfg.mass]) 0
  constructor
  rintro s b ⟨rfl, hb⟩
  simpa using hh.le_wp _ b ⟨rfl, by simp [Cfg.mass], by simpa using hb⟩

end Complexity.StackMachine.Program
