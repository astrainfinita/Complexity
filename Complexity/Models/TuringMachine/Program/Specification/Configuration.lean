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

variable {κ : Type} {Γ α β : Type} [Inhabited Γ] {xs : Array Γ}

/-- Interpret a program on tape configurations, without a visitation ghost. -/
def cfgSemantics (xs : Array Γ) :
    Complexity.Program.Semantics (Γ × (κ → Γ)) (Action κ Γ Unit) (Op κ Γ) Op.Result
      (Cfg κ Γ Unit xs) where
  eval := eval
  observe := Controller.observe
  act := apply

/-- A local action consumes one transition. -/
@[spec]
theorem cfg_spec_act (a : Action κ Γ Unit) (xs : Array Γ) (s : Cfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((act a).verify (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = apply a s ∧ c = b - 1) x :=
  Complexity.Program.spec_perform (Op.act a) (cfgSemantics xs) s b h x

/-- Reading the input preserves the tape configuration. -/
@[spec]
theorem cfg_spec_readInput [FinEnum Γ] (xs : Array Γ) (s : Cfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple (readInput.verify (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = s.inputSymbol ∧ t = s ∧ c = b - 1) x := by
  simpa only [readInput, Op.Result, cfgSemantics, eval, idle_apply, Cfg.observe_def] using
    Complexity.Program.spec_perform (Op.readInput (κ := κ) (Γ := Γ) inferInstance)
      (cfgSemantics xs) s b h x

/-- Reading a work symbol preserves the tape configuration. -/
@[spec]
theorem cfg_spec_read [FinEnum Γ] (i : κ) (xs : Array Γ) (s : Cfg κ Γ Unit xs)
    (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((read i).verify (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = s.workSymbols i ∧ t = s ∧ c = b - 1) x := by
  simpa only [read, Op.Result, cfgSemantics, eval, idle_apply, Cfg.observe_def] using
    Complexity.Program.spec_perform (Op.read (Γ := Γ) inferInstance i) (cfgSemantics xs) s b h x

/-- A batch observation records its actual values without enumerating possible vectors. -/
@[spec]
theorem cfg_spec_observeBits {n : ℕ} (f : (Γ × (κ → Γ)) → Fin n → Bool)
    (xs : Array Γ) (s : Cfg κ Γ Unit xs) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((observeBits f).verify (cfgSemantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun v t c ↦ v = Vector.ofFn (f (s.inputSymbol, s.workSymbols)) ∧
        t = s ∧ c = b - 1) x := by
  simpa only [observeBits, Op.Result, cfgSemantics, eval, idle_apply, Cfg.observe_def] using
    Complexity.Program.spec_perform (Op.observeBits n f) (cfgSemantics xs) s b h x

/-- A total loop rule on configurations; the dispatcher consumes one time credit. -/
@[spec]
theorem cfg_spec_repeatUntil (p : Program κ Γ Bool)
    (I : Complexity.Program.Invariant (Cfg κ Γ Unit xs) (ℕ → Prop))
    (Q : Unit → Cfg κ Γ Unit xs → ℕ → Prop)
    (hp : ∀ s b, I s b → 0 < b)
    (hb : Triple (p.verify (cfgSemantics xs)) (fun s b ↦ I s (b + 1))
      (fun r s b ↦ if r then Q () s b else I s b) ()) :
    Triple ((repeatUntil p).verify (cfgSemantics xs)) (fun s b ↦ I s b) Q () :=
  Complexity.Program.spec_repeatUntil_nop idle p (cfgSemantics xs) I Q () idle_apply hp hb

/-- A finite-value loop requires only the carried value, tapes, and remaining budget. -/
@[spec]
theorem cfg_spec_loopOn [FinEnum α] [FinEnum β]
    (p : α → Program κ Γ (α ⊕ β)) (i : α)
    (I : Complexity.Program.Invariant α (Cfg κ Γ Unit xs → ℕ → Prop))
    (Q : β → Cfg κ Γ Unit xs → ℕ → Prop)
    (hp : ∀ i s b, I i s b → 0 < b)
    (hb : ∀ i, Triple ((p i).verify (cfgSemantics xs)) (fun s b ↦ I i s (b + 1))
      (fun r s b ↦ match r with | .inl j => I j s b | .inr j => Q j s b) ()) :
    Triple ((Complexity.Program.loopOn idle p i).verify (cfgSemantics xs)) (I i) Q () :=
  Complexity.Program.spec_loopOn_nop idle p i (cfgSemantics xs) I Q idle_apply hp hb

end Complexity.TM.Program
