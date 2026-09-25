/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Correctness
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

variable {κ : Type} {Γ α : Type} [Inhabited Γ]

/-- Interpret local actions on tape data and ghost interval endpoints. -/
@[simps eval observe act]
def semantics (xs : Array Γ) :
    Complexity.Program.Semantics (Γ × (κ → Γ)) (Action κ Γ Unit) (Op κ Γ) Op.Result
      (TrackedCfg κ Γ Unit xs) where
  eval := eval
  observe := Controller.observe
  act := apply

/-- An idle step preserves the configuration and its recorded intervals. -/
@[simp]
theorem apply_idle {xs : Array Γ} (s : TrackedCfg κ Γ Unit xs) :
    apply (idle (κ := κ) (Γ := Γ)) s = s := by
  apply TrackedCfg.ext (idle_apply s.cfg)
  funext i
  rw [apply_visited, idle_apply]
  exact sup_eq_left.mpr (s.head_mem i)

/-- A head move preserves a footprint whenever its new position remains inside it. -/
theorem moveAction_within [DecidableEq κ] {xs : Array Γ} (j : κ) (d : SignType)
    (s : TrackedCfg κ Γ Unit xs) (L R : κ → ℤ)
    (hF : s.Within L R)
    (hj : (apply (moveAction (Γ := Γ) j d) s.cfg).workPos j ∈ Set.Icc (L j) (R j)) :
    (apply (moveAction (Γ := Γ) j d) s).Within L R := by
  apply (s.within_apply_iff _ L R).mpr
  refine ⟨hF, ?_⟩
  intro i
  by_cases hi : i = j
  · subst i; exact hj
  · simpa [hi] using hF.head i

/-- A total loop rule on traces; the dispatcher consumes one time credit. -/
@[spec]
theorem spec_repeatUntil {xs : Array Γ} (p : Program κ Γ Bool)
    (I : Complexity.Program.Invariant (TrackedCfg κ Γ Unit xs) (ℕ → Prop))
    (Q : Unit → TrackedCfg κ Γ Unit xs → ℕ → Prop)
    (hp : ∀ s b, I s b → 0 < b)
    (hb : Triple (p.verify (semantics xs)) (fun s b ↦ I s (b + 1))
      (fun r s b ↦ if r then Q () s b else I s b) ()) :
    Triple ((repeatUntil p).verify (semantics xs)) (fun s b ↦ I s b) Q () :=
  Complexity.Program.spec_repeatUntil_nop idle p (semantics xs) I Q ()
    apply_idle hp hb

/-- A local action consumes one transition and updates the visited endpoints. -/
@[spec]
theorem spec_act (a : Action κ Γ Unit) (xs : Array Γ) (s : TrackedCfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((act a).verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = () ∧ t = apply a s ∧ c = b - 1) x :=
  Complexity.Program.spec_perform (Op.act a) (semantics xs) s b h x

/-- Reading the input preserves the trace and consumes one transition. -/
@[spec]
theorem spec_readInput [FinEnum Γ] (xs : Array Γ) (s : TrackedCfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple (readInput.verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = s.cfg.inputSymbol ∧ t = s ∧ c = b - 1) x := by
  simpa [readInput, eval] using
    Complexity.Program.spec_perform (Op.readInput (κ := κ) (Γ := Γ) inferInstance)
      (semantics xs) s b h x

/-- Reading a work symbol preserves the trace and consumes one transition. -/
@[spec]
theorem spec_read [FinEnum Γ] (i : κ) (xs : Array Γ) (s : TrackedCfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((read i).verify (semantics xs)) (fun t c => t = s ∧ c = b)
      (fun r t c => r = s.cfg.workSymbols i ∧ t = s ∧ c = b - 1) x := by
  simpa [read, eval] using
    Complexity.Program.spec_perform (Op.read (Γ := Γ) inferInstance i)
      (semantics xs) s b h x

/-- The state used to verify a complete program on an input. -/
def initial (xs : Array Γ) : TrackedCfg κ Γ Unit xs := ((rawExecution xs.toList).init ()).track

/-- A program-level total specification suffices for the compiled machine's resource bound. -/
theorem computesInTimeAndSpace [Fintype κ] {p : Program κ Γ α} {xs ys : Array Γ} {t s : ℕ}
    {P : TrackedCfg κ Γ Unit xs → ℕ → Prop}
    (h : Triple (p.verify (semantics xs)) P
      (fun _ v _ ↦ v.cfg.output = ys ∧ v.space ≤ s) ())
    (hp : P (initial xs) t) :
    (compile p).ComputesInTimeAndSpace xs.toList ys.toList t s := by
  obtain ⟨n, a, v, hn, he, ho, hs⟩ := Complexity.Program.exec_of_spec h hp
  exact computesInTimeAndSpace_of_exec p he hn ho hs

section Configuration

variable {xs : Array Γ}

/-- Forget the history in an already verified total specification. -/
theorem cfg_of_trace {p : Program κ Γ α}
    {P : TrackedCfg κ Γ Unit xs → ℕ → Prop} {Q : α → TrackedCfg κ Γ Unit xs → ℕ → Prop}
    {P' : Cfg κ Γ Unit xs → ℕ → Prop} {Q' : α → Cfg κ Γ Unit xs → ℕ → Prop}
    (h : Triple (p.verify (semantics xs)) P Q ())
    (hp : ∀ c b, P' c b → P c.track b)
    (hq : ∀ a s b, Q a s b → Q' a s.cfg b) :
    Triple (p.verify (cfgSemantics xs)) P' Q' () := by
  exact Complexity.Program.spec_simulate (fun s c ↦ c = s.cfg)
    (by rintro s _ rfl; rfl) (by rintro a s _ rfl; rfl) h
    (fun c b hc ↦ ⟨c.track, hp c b hc, rfl⟩)
    (by rintro a s _ b rfl hs; exact hq a s b hs)

/-- A total time specification gives the compiled machine's time and coarse space bounds. -/
theorem cfg_computesInTimeAndSpace [Fintype κ] {p : Program κ Γ α} {ys : Array Γ} {t : ℕ}
    {P : Cfg κ Γ Unit xs → ℕ → Prop}
    (h : Triple (p.verify (cfgSemantics xs)) P (fun _ c _ ↦ c.output = ys) ())
    (hp : P ((rawExecution xs.toList).init ()) t) :
    (compile p).ComputesInTimeAndSpace xs.toList ys.toList t (Fintype.card κ * (t + 1)) := by
  obtain ⟨n, a, c, hn, he, ho⟩ := Complexity.Program.exec_of_spec h hp
  obtain ⟨v, hv, hr⟩ := Complexity.Program.Exec.lift TrackedCfg.cfg
    (e' := semantics xs)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) he (((rawExecution xs.toList).init ()).track) rfl
  obtain ⟨e, _, he⟩ := run_compile (Complexity.Program.Exec.compile hr)
  apply TM.ReachesInTimeAndSpace.computesInTimeAndSpace
    (M := compile p) (d := v.cfg.mapState (fun _ ↦ Sum.inr e)) ?_ (by rfl)
    (by change v.cfg.output = ys; rw [hv]; exact ho)
  refine ⟨n, hn, ?_, ?_⟩
  · exact ((compile p).tracked_runFrom_cfg _ n).symm.trans (congrArg TrackedCfg.cfg he)
  · exact ((compile p).spaceUsed_le_time _ n).trans
      (Nat.mul_le_mul_left (Fintype.card κ) (by omega))

end Configuration

end Complexity.TM.Program
