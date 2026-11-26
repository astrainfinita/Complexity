/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.StackMachine.Circuit

open Complexity StackMachine

namespace StackCircuitTest

/-- Both labels halt in one step; only label `1` emits `true`. -/
def guess : StackMachine BinaryChoice Empty Bool Bool where
  q₀ := false
  halt q := q
  transition _ _ b :=
    (true, { inputMove := 0, work := Empty.elim, output := if b = 1 then some true else none })

-- Guards `eval_runCircuit`: along label `1`, the one-step run halts with output `[true]`.
example : (guess.runCircuit [] [true] 1 FinEnum.equiv FinEnum.equiv).eval (fun _ ↦ true) 0 =
    true := by
  rw [eval_runCircuit]
  simp [Controller.stepAlong, Controller.Halted, guess, finTwoEquiv]

-- Guards `exists_eval_runCircuit_iff` under direct forward application with explicit `xs`.
example : ∃ x, (guess.runCircuit [] [true] 1 FinEnum.equiv FinEnum.equiv).eval x 0 = true :=
  (exists_eval_runCircuit_iff guess [] [true] 1 FinEnum.equiv FinEnum.equiv).mpr
    ⟨_, (Controller.mem_returns_runWith_multiset_iff _ _ _ _).mpr ⟨![1], rfl⟩, by
      simp [Controller.stepAlong, Controller.Halted, guess]⟩

-- Guards `exists_eval_runCircuit_iff` at `t = 0`: without a step nothing has halted.
example : ¬∃ x, (guess.runCircuit [] [true] 0 FinEnum.equiv FinEnum.equiv).eval x 0 = true := by
  rw [exists_eval_runCircuit_iff]
  simp [Controller.Halted, guess]

-- Guards `size_runCircuit_le`, `RunCircuit.card_wire`, and `RunCircuit.card_actionBit`:
-- with 8 wires, 7 control signals, and 3 local bits, the one-step gate bound is 722.
example : (guess.runCircuit [] [true] 1 FinEnum.equiv FinEnum.equiv).size ≤ 722 := by
  refine (size_runCircuit_le guess [] [true] 1 FinEnum.equiv FinEnum.equiv).trans ?_
  rw [RunCircuit.card_wire, RunCircuit.card_actionBit]
  decide

/-- One step pushes the input symbol on the work stack, moves right, and halts; label `1` also
emits the input symbol. -/
def copyGuess : StackMachine BinaryChoice Unit Bool Bool where
  q₀ := false
  halt q := q
  transition _ o b :=
    (true, { inputMove := 1, work := fun _ ↦ o.1.elim .nop .push
             output := if b = 1 then o.1 else none })

-- Guards `eval_runCircuit` on a non-empty input with a halted padding step.
example : (copyGuess.runCircuit [true] [true] 2 FinEnum.equiv FinEnum.equiv).eval
    ![true, false] 0 = true := by
  rw [eval_runCircuit]
  simp [Controller.stepAlong, Controller.Halted, copyGuess, finTwoEquiv]

-- Guards `exists_eval_runCircuit_iff` with a halted padding step: the run halts after one of its
-- two steps, and the label of the second step is ignored.
example : ∃ x, (copyGuess.runCircuit [true] [true] 2 FinEnum.equiv FinEnum.equiv).eval x 0 =
    true := by
  rw [exists_eval_runCircuit_iff]
  refine ⟨_, (Controller.mem_returns_runWith_multiset_iff _ _ _ _).mpr ⟨![1, 0], rfl⟩, ?_⟩
  simp [Controller.stepAlong, Controller.Halted, copyGuess]

-- Guards `exists_eval_runCircuit_iff`: the emitted symbol is read from the input, so `[false]`
-- is never accepted.
example : ¬∃ x, (copyGuess.runCircuit [true] [false] 2 FinEnum.equiv FinEnum.equiv).eval x 0 =
    true := by
  simp only [exists_eval_runCircuit_iff, Controller.mem_returns_runWith_multiset_iff]
  simp [Fin.exists_fin_succ_pi, Fin.exists_fin_two, Controller.stepAlong, Controller.Halted,
    copyGuess]

/-- Push input symbols onto a single work stack until the right boundary, bump once against the
right boundary, move left, then pop and emit the stack in reverse order (ignoring labels). -/
def pushPop : StackMachine BinaryChoice Unit Bool (Fin 4) where
  q₀ := 0
  halt q := q = 3
  transition q o _ := match q with
    | 0 => match o.1 with
      | some a => (0, { inputMove := 1, work := fun _ ↦ .push a, output := none })
      | none => (1, { inputMove := 1, work := fun _ ↦ .nop, output := none })
    | 1 => (2, { inputMove := -1, work := fun _ ↦ .nop, output := none })
    | 2 => match o.2 () with
      | some a => (2, { inputMove := 0, work := fun _ ↦ .pop, output := some a })
      | none => (3, .idle)
    | 3 => (3, .idle)

-- Guards `eval_runCircuit` across stack depth > 1, right-boundary clamping, left movement, and
-- stack popping: `[true, false]` is reversed into `[false, true]` in 7 steps.
example : (pushPop.runCircuit [true, false] [false, true] 7 FinEnum.equiv FinEnum.equiv).eval
    (fun _ ↦ false) 0 = true := by
  rw [eval_runCircuit]
  simp [Controller.stepAlong, Controller.Halted, pushPop, Input.movePos, Op.apply]

-- Guards that `pushPop` rejects the unreversed output `[true, false]`.
example : (pushPop.runCircuit [true, false] [true, false] 7 FinEnum.equiv FinEnum.equiv).eval
    (fun _ ↦ false) 0 = false := by
  rw [eval_runCircuit]
  simp [Controller.stepAlong, Controller.Halted, pushPop, Input.movePos, Op.apply]

end StackCircuitTest
