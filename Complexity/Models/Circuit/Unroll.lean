/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Composition
public import Mathlib.Data.List.OfFn

/-! # Bounded execution with fresh choice inputs

A step reads `n` state wires and one choice wire. Its `t`-step unfolding reads the initial
state followed by `t` independent choices, and returns the final state.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {M : Type w} {n : ℕ}

/-- Repeat a state transition, using a different input wire for each step's choice. -/
def unroll (step : Circuit L (n + 1) n) : (t : ℕ) → Circuit L (n + t) n
  | 0 => id L n
  | t + 1 =>
      ((step.unroll t).relabel Fin.castSucc).keepInputs.comp
        (step.relabel (Fin.snoc (Fin.natAdd (n + (t + 1)))
          (Fin.castAdd n (Fin.last (n + t)))))

@[simp] theorem size_unroll (step : Circuit L (n + 1) n) (t : ℕ) :
    (step.unroll t).size = t * step.size := by
  induction t with
  | zero => simp [unroll]
  | succ t ih => simp [unroll, ih, Nat.succ_mul]

/-- The last layer reads the last choice and the state produced by all earlier layers. -/
@[simp] theorem evalWith_unroll_succ (step : Circuit L (n + 1) n) (t : ℕ)
    (ops : ∀ {k}, L.Functions k → (Fin k → M) → M) (x : Fin (n + (t + 1)) → M) :
    (step.unroll (t + 1)).evalWith ops x =
      step.evalWith ops (Fin.snoc ((step.unroll t).evalWith ops (x ∘ Fin.castSucc))
        (x (Fin.last (n + t)))) := by
  simp only [unroll, evalWith_comp, evalWith_keepInputs, evalWith_relabel]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def]

/-- Unfolding agrees with sequentially applying the step to the supplied choice sequence. -/
theorem evalWith_unroll (step : Circuit L (n + 1) n) (t : ℕ)
    (ops : ∀ {k}, L.Functions k → (Fin k → M) → M)
    (x : Fin n → M) (b : Fin t → M) :
    (step.unroll t).evalWith ops (Fin.append x b) =
      (List.ofFn b).foldl (fun state choice => step.evalWith ops (Fin.snoc state choice)) x := by
  induction t with
  | zero =>
      simp only [unroll, List.ofFn_zero, List.foldl_nil]
      funext i
      change Fin.append x b (Fin.castAdd 0 i) = x i
      exact Fin.append_left x b i
  | succ t ih =>
      have hx : Fin.append x b ∘ Fin.castSucc = Fin.append x (fun i => b i.castSucc) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · change Fin.append x b (Fin.castAdd (t + 1) j) = _
          simp
        · simp
      have hb : Fin.append x b (Fin.last (n + t)) = b (Fin.last t) := by
        exact Fin.append_right x b (Fin.last t)
      rw [evalWith_unroll_succ, hx, ih, List.ofFn_succ']
      simp [hb]

theorem eval_unroll [L.Structure M] (step : Circuit L (n + 1) n) (t : ℕ)
    (x : Fin n → M) (b : Fin t → M) :
    (step.unroll t).eval (Fin.append x b) =
      (List.ofFn b).foldl (fun state choice => step.eval (Fin.snoc state choice)) x :=
  step.evalWith_unroll t Structure.funMap x b

end Complexity.Circuit
