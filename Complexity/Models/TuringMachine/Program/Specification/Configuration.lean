/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Loop
public import Complexity.Models.TuringMachine.Program.Specification.Basic

/-!
# Specifications using only tape configurations

Programs can be verified using only their tape data and remaining time budget.
These rules are independent of visitation history and compiler correctness.
-/

@[expose] public section

namespace Complexity.TM.Program

open Std.WP

variable {F : Type → Type} {κ : Type} {Γ : Type} [Inhabited Γ] {xs : Array Γ}

/-- Interpret a program on tape configurations, without a visitation ghost. -/
@[simps eval observe act]
def cfgSemantics (xs : Array Γ) :
    Program.Semantics (Γ × (κ → Γ)) (Action κ Γ) (Op κ Γ) Op.Result
      (Cfg κ Γ xs) where
  eval := eval
  observe := Controller.observe
  act := apply

section Verify

variable {m : Type → Type} [Monad m] {Q : MonadQuant m} [MonadLiftT F m]

/-- A local action consumes one transition. -/
@[spec]
theorem cfg_spec_act (a : Action κ Γ) (xs : Array Γ) (s : Cfg κ Γ xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((act (F := F) a).verifyWith m Q (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = apply a s ∧ c = b - 1) x :=
  Program.spec_perform (Op.act a) (cfgSemantics xs) s b h x

/-- Reading the input preserves the tape configuration. -/
@[spec]
theorem cfg_spec_readInput [FinEnum Γ] (xs : Array Γ) (s : Cfg κ Γ xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((readInput (F := F)).verifyWith m Q (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = s.inputSymbol ∧ t = s ∧ c = b - 1) x := by
  simpa [readInput, eval] using
    Program.spec_perform (Op.readInput inferInstance) (cfgSemantics xs) s b h x

/-- Reading a work symbol preserves the tape configuration. -/
@[spec]
theorem cfg_spec_read [FinEnum Γ] (i : κ) (xs : Array Γ) (s : Cfg κ Γ xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((read (F := F) i).verifyWith m Q (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = s.workSymbols i ∧ t = s ∧ c = b - 1) x := by
  simpa [read, eval] using Program.spec_perform (Op.read inferInstance i) (cfgSemantics xs) s b h x

/-- A total loop rule on configurations; the dispatcher consumes one time credit. -/
@[spec]
theorem cfg_spec_repeatUntil (p : TM.Program F κ Γ Bool)
    (I : Program.Invariant (Cfg κ Γ xs) (ℕ → Prop))
    (R : Unit → Cfg κ Γ xs → ℕ → Prop)
    (hp : ∀ s b, I s b → 0 < b)
    (hb : Triple (p.verifyWith m Q (cfgSemantics xs)) (fun s b ↦ I s (b + 1))
      (fun r s b ↦ if r then R () s b else I s b) ()) :
    Triple ((repeatUntil p).verifyWith m Q (cfgSemantics xs)) (fun s b ↦ I s b) R () :=
  Program.spec_repeatUntilWith_nop idle p (cfgSemantics xs) I R () idle_apply hp hb

end Verify

end Complexity.TM.Program
