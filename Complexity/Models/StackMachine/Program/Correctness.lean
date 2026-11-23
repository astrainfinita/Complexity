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

/-- A macro's time bound also bounds its temporary space, without inspecting its internals.
Reserved credits survive, so this rule composes with amortized time arguments. -/
theorem spec_history [Fintype κ] {p : StackMachine.Program Id κ Γ α}
    {c : Cfg κ Γ xs} {n r S : ℕ} {P : α → Cfg κ Γ xs → Prop}
    (h : Triple (p.verify (semantics xs)) (fun s b ↦ s = c ∧ n ≤ b)
      (fun a s b ↦ P a s ∧ r ≤ b) ())
    (hs : c.mass + Fintype.card κ * n ≤ S) (q : ℕ) :
    Triple (p.verify (historySemantics xs))
      (fun s b ↦ s.last = c ∧ s.configSup Cfg.mass ≤ S ∧ n + q ≤ b)
      (fun a s b ↦ P a s.last ∧ s.configSup Cfg.mass ≤ S ∧ r + q ≤ b) () := by
  constructor
  rintro s b ⟨hc, hS, hb⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_add_right_le hb)
  have he := (Program.execWithinWith_of_spec h (s := c) (b := n) ⟨rfl, le_rfl⟩).add_budget d
  -- Each transition adds at most `Fintype.card κ` to the mass, so the `u` steps taken bound it.
  have hi := (he.simulate (e' := historySemantics xs) (fun x y ↦ y.last = x)
    (fun _ _ h ↦ h ▸ rfl) (fun _ _ _ h ↦ h ▸ History.last_snoc _ _) s hc rfl).inv
    (I := fun (t : History (Cfg κ Γ xs) (Action κ Γ)) b' ↦
      ∃ u, b' + u = n + d ∧ t.last.mass ≤ c.mass + Fintype.card κ * u ∧
        t.configSup Cfg.mass ≤ s.configSup Cfg.mass ⊔ (c.mass + Fintype.card κ * u))
    (by
      rintro a t b' ⟨u, hu, hm, hsup⟩
      have hm' : (apply a t.last).mass ≤ c.mass + Fintype.card κ * (u + 1) := by
        rw [Nat.mul_add_one, ← Nat.add_assoc]
        exact (t.last.mass_apply_le a).trans (Nat.add_le_add_right hm _)
      simp only [historySemantics_act, History.apply_def, History.configSup_snoc,
        History.last_snoc]
      exact ⟨u + 1, by rwa [Nat.add_assoc, Nat.add_comm 1 u] at hu, hm',
        sup_le (hsup.trans (sup_le_sup_left
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_succ u)) _) _))
          (le_sup_of_le_right hm')⟩)
    ⟨0, rfl, hc ▸ Nat.le_add_right _ _, le_sup_left⟩
  refine hi.mono ?_
  rintro a t b' ⟨⟨_, rfl, c', ⟨hP, hr⟩, rfl⟩, u, hu, -, hsup⟩
  have hun : u ≤ n := by clear * - hu; omega
  exact ⟨hP, hsup.trans (sup_le hS ((Nat.add_le_add_left (Nat.mul_le_mul_left _ hun) _).trans hs)),
    Nat.add_le_add hr (Nat.le_of_add_le_add_left hb)⟩

/-- A history specification supplies independent time and peak-space bounds. -/
theorem computesWithin_history [Fintype κ] {p : StackMachine.Program Id κ Γ α}
    {xs ys : List Γ} {t s : ℕ}
    (h : Triple (p.verify (historySemantics xs.toArray))
      (fun h b ↦ h = History.nil (Cfg.init κ xs) ∧ t ≤ b)
      (fun _ h _ ↦ h.last.output = ys.toArray ∧ h.configSup Cfg.mass ≤ s) ()) :
    p.compile.ComputesWithin xs ys t s := by
  obtain ⟨e, v, hr, -, -, ho, hs⟩ := Program.Syntax.ExecWithin.runFrom_compile idle
    (Program.execWithinWith_of_spec h ⟨rfl, le_rfl⟩)
  rw [Controller.runFrom_prod_nil, Prod.mk.injEq] at hr
  have hl := congrArg History.last hr.2
  rw [History.last_snd, Controller.last_runHistoryFrom] at hl
  exact .of_halted t ((congrArg p.compile.halt hr.1).trans rfl) ((congrArg Cfg.output hl).trans ho)
    ((History.length_snd _).trans_le (p.compile.length_runHistory_le _ t))
    ((congrArg (·.configSup Cfg.mass) hr.2).le.trans hs)

/-- A total stack-program specification yields native computation and resource bounds. -/
theorem computesWithin [Fintype κ] (p : StackMachine.Program Id κ Γ α)
    {xs ys : List Γ} {t : ℕ}
    (h : Triple (p.verify (semantics xs.toArray))
      (fun c b ↦ c = Cfg.init κ xs ∧ t ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray) ()) :
    (compile p).ComputesWithin xs ys t (Fintype.card κ * t) := by
  obtain ⟨e, c, hr, -, -, ho⟩ := Program.Syntax.ExecWithin.runFrom_compile idle
    (Program.execWithinWith_of_spec h ⟨rfl, le_rfl⟩)
  exact .of_run (n := t) (congrArg (compile p).halt (congrArg Prod.fst hr))
    ((congrArg (fun r ↦ r.2.output) hr).trans ho) le_rfl

end Complexity.StackMachine.Program
