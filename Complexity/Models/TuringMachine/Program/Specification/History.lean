/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Correctness
public import Complexity.Control.Controller.RunHistory
public import Complexity.Models.TuringMachine.Program.Specification.Configuration
public import Complexity.Control.Program.Loop

/-!
# Verifying programs independently of their compiled controllers

Assertions describe tape data, visited intervals, and remaining time budget.
The final theorem turns a total program specification into the usual machine specification.
The fixed input is supplied to the interpretation only; it does not change the compiled graph.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP
open Controller (History)

variable {F : Type → Type} {κ : Type} {Γ α : Type} [Inhabited Γ]

/-- Interpret local actions on tape data and visited intervals. -/
@[simps eval observe act]
def semantics (xs : Array Γ) :
    Program.Semantics (Γ × (κ → Γ)) (Action κ Γ) (Op κ Γ) Op.Result
      (History (Cfg κ Γ xs) (Action κ Γ)) where
  eval := eval
  observe := Controller.observe
  act := apply

@[simp 1100] theorem visited_snoc_idle {xs : Array Γ}
    (s : History (Cfg κ Γ xs) (Action κ Γ)) :
    (s.snoc idle).visited = s.visited := by
  rw [History.visited_snoc]
  simp only [idle_apply]
  exact sup_eq_left.mpr s.head_mem

/-- A total loop rule for assertions about tape data and visited intervals. -/
@[spec]
theorem spec_repeatUntil {xs : Array Γ} (p : TM.Program F κ Γ Bool)
    (I : Program.Invariant (Cfg κ Γ xs) ((κ → NonemptyInterval ℤ) → ℕ → Prop))
    (Q : Unit → History (Cfg κ Γ xs) (Action κ Γ) → ℕ → Prop)
    (hp : ∀ (s : History (Cfg κ Γ xs) (Action κ Γ)) b,
      I s.last s.visited b → 0 < b)
    (hb : Triple (p.verify (semantics xs)) (fun s b ↦ I s.last s.visited (b + 1))
      (fun r s b ↦ if r then Q () s b else I s.last s.visited b) ()) :
    Triple ((repeatUntil p).verify (semantics xs)) (fun s b ↦ I s.last s.visited b) Q () :=
  Program.spec_repeatUntilWith_of_invariant idle p (semantics xs)
    (fun s ↦ I s.last s.visited) Q () (fun s _ hs ↦ by simpa using hs) hp hb

/-- A local action consumes one transition and updates the visited endpoints. -/
@[spec]
theorem spec_act (a : Action κ Γ) (xs : Array Γ)
    (s : History (Cfg κ Γ xs) (Action κ Γ))
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((act (F := F) a).verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = () ∧ t = apply a s ∧ c = b - 1) x :=
  Program.spec_perform (Op.act a) (semantics xs) s b h x

/-- Reading the input preserves the tape configuration and consumes one transition. -/
@[spec]
theorem spec_readInput [FinEnum Γ] (xs : Array Γ)
    (s : History (Cfg κ Γ xs) (Action κ Γ))
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((readInput (F := F)).verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = s.last.inputSymbol ∧ t = s.snoc idle ∧ c = b - 1) x := by
  simpa [readInput, eval] using
    Program.spec_perform (Op.readInput inferInstance)
      (semantics xs) s b h x

/-- Reading a work symbol preserves the tape configuration and consumes one transition. -/
@[spec]
theorem spec_read [FinEnum Γ] (i : κ) (xs : Array Γ)
    (s : History (Cfg κ Γ xs) (Action κ Γ))
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((read (F := F) i).verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = s.last.workSymbols i ∧ t = s.snoc idle ∧ c = b - 1) x := by
  simpa [read, eval] using
    Program.spec_perform (Op.read inferInstance i)
      (semantics xs) s b h x

/-- A program-level total specification suffices for the compiled machine's resource bound. -/
theorem computesWithin [Fintype κ] {p : TM.Program Id κ Γ α} {xs ys : Array Γ} {t s : ℕ}
    {P : History (Cfg κ Γ xs) (Action κ Γ) → ℕ → Prop}
    (h : Triple (p.verify (semantics xs)) P
      (fun _ v _ ↦ v.last.output = ys ∧ v.space ≤ s) ())
    (hp : P (History.nil (Cfg.init κ xs.toList)) t) :
    (compile p).ComputesWithin xs.toList ys.toList t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Program.exec_of_spec h hp
  exact computesWithin_of_exec p he hn ho hs

section Configuration

variable {xs : Array Γ}

/-- Forget the history in an already verified total specification. -/
theorem cfg_of_history {p : TM.Program F κ Γ α}
    {P : History (Cfg κ Γ xs) (Action κ Γ) → ℕ → Prop}
    {Q : α → History (Cfg κ Γ xs) (Action κ Γ) → ℕ → Prop}
    {P' : Cfg κ Γ xs → ℕ → Prop} {Q' : α → Cfg κ Γ xs → ℕ → Prop}
    (h : Triple (p.verify (semantics xs)) P Q ())
    (hp : ∀ c b, P' c b → P (History.nil c) b)
    (hq : ∀ a s b, Q a s b → Q' a s.last b) :
    Triple (p.verify (cfgSemantics xs)) P' Q' () := by
  exact Program.spec_simulate (fun s c ↦ c = s.last)
    (by rintro s _ rfl; rfl) (by rintro a s _ rfl; simp) h
    (fun c b hc ↦ ⟨History.nil c, hp c b hc, rfl⟩)
    (by rintro a s _ b rfl hs; exact hq a s b hs)

/-- A total time specification gives the compiled machine's time and coarse space bounds. -/
theorem cfg_computesWithin [Fintype κ] {p : TM.Program Id κ Γ α} {ys : Array Γ} {t : ℕ}
    {P : Cfg κ Γ xs → ℕ → Prop}
    (h : Triple (p.verify (cfgSemantics xs)) P (fun _ c _ ↦ c.output = ys) ())
    (hp : P (Cfg.init κ xs.toList) t) :
    (compile p).ComputesWithin xs.toList ys.toList t (Fintype.card κ * (t + 1)) := by
  obtain ⟨n, a, c, hn, he, ho⟩ := Program.exec_of_spec h hp
  obtain ⟨v, hv, hr⟩ := Program.Exec.lift History.last
    (e' := semantics xs)
    (fun _ ↦ rfl) (fun _ _ ↦ by simp) he (History.nil (Cfg.init κ xs.toList)) rfl
  exact (computesWithin_of_exec p hr hn (by rw [hv]; exact ho) le_rfl).space_of_time

end Configuration

end Complexity.TM.Program
