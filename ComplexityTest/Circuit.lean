/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic
import Complexity.Models.Circuit.Compile
import Complexity.Models.Circuit.Evaluation
import Complexity.Models.Circuit.Term
import Complexity.Models.Circuit.Unroll
import Complexity.Resources.Circuit.Basic
import Complexity.Resources.Circuit.Compile
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Tactic.FinCases

open FirstOrder FirstOrder.Language Complexity

namespace Complexity.CircuitTest

-- The three gates compute z = x + y, w = z * z, and w + z, retaining all three outputs.
private def arithmetic : Circuit Language.ring 2 3 :=
  .gate FirstOrder.Ring.addFunc ![0, 1]
    (.gate FirstOrder.Ring.mulFunc ![2, 2]
      (.gate FirstOrder.Ring.addFunc ![3, 2] (.outputs ![2, 3, 4])))

example : arithmetic.size = 3 := rfl
example : arithmetic.depth = 3 := by decide
example : arithmetic.FanInAtMost 2 := by decide
example : ¬arithmetic.FanInAtMost 1 := by decide

section Ring

variable {R : Type*} [Ring R] [FirstOrder.Ring.CompatibleRing R]

private theorem arithmetic_spec (x : Fin 2 → R) :
    arithmetic.eval x = ![x 0 + x 1, (x 0 + x 1) * (x 0 + x 1),
      (x 0 + x 1) * (x 0 + x 1) + (x 0 + x 1)] := by
  funext i
  fin_cases i <;> simp [arithmetic, Function.comp_def, Fin.snoc]

-- Term unfolding uses the existing ring semantics.
example (x : Fin 2 → R) :
    (arithmetic.toTerms 2).realize x = (x 0 + x 1) * (x 0 + x 1) + (x 0 + x 1) := by
  simp [arithmetic_spec]

end Ring

section Int

local instance : FirstOrder.Ring.CompatibleRing ℤ := FirstOrder.Ring.compatibleRingOfRing ℤ

example : arithmetic.evalVector (M := ℤ) #v[2, 3] = #v[5, 25, 30] := by decide

-- A term round trip preserves values, while expansion duplicates the shared sum.
example : (Circuit.ofTerm (arithmetic.toTerms 2)).evalVector (M := ℤ) #v[2, 3] = #v[30] := by
  decide
example : (Circuit.ofTerm (arithmetic.toTerms 2)).size = 5 := by decide

-- Output selection is free and dead gates contribute to size but not to output depth.
example : (arithmetic.mapOutputs ![0, 0]).size = 3 := rfl
example : (arithmetic.mapOutputs ![0, 0]).depth = 1 := by decide
example : (arithmetic.mapOutputs ![0, 0]).evalVector (M := ℤ) #v[2, 3] = #v[5, 5] := by decide

example : (arithmetic.mapOutputs (Fin.elim0 : Fin 0 → Fin 3)).depth = 0 := by simp

-- Wiring and sequential composition retain sharing, with no cost for copying outputs.
private def duplicate : Circuit Language.ring 1 2 := .outputs ![0, 0]
private def add : Circuit Language.ring 2 1 := .ofGate FirstOrder.Ring.addFunc ![0, 1]

example : (duplicate.comp add).size = 1 := by simp [duplicate, add]
example : (duplicate.comp add).evalVector (M := ℤ) #v[7] = #v[14] := by decide

example : (add.fanout (Circuit.id Language.ring 2)).evalVector (M := ℤ) #v[2, 3] =
    #v[5, 2, 3] := by
  decide

example : (add.fanout add).size = 2 := by simp [add]

example : (add.unroll 2).evalVector (M := ℤ) #v[10, 2, 3] = #v[15] := by decide
example : (add.unroll 2).size = 2 := by simp [add]
example : (add.unroll 0).evalVector (M := ℤ) #v[10] = #v[10] := by decide

-- A circuit can have no inputs, with constant gates providing its output values.
private def constant : Circuit Language.ring 0 2 :=
  .gate FirstOrder.Ring.zeroFunc ![]
    (.gate FirstOrder.Ring.oneFunc ![] (.outputs ![0, 1]))

example : constant.size = 2 := rfl
example : constant.depth = 1 := by decide
example : constant.FanInAtMost 0 := by decide
example : constant.evalVector (M := ℤ) #v[] = #v[0, 1] := by decide

end Int

section Boolean

-- The same core supports the Boolean algebra language added in the preceding commit.
private def andNot : Circuit Language.booleanAlgebra 2 2 :=
  .gate FirstOrder.BooleanAlgebra.infFunc ![0, 1]
    (.gate FirstOrder.BooleanAlgebra.complFunc ![2] (.outputs ![2, 3]))

example : andNot.evalVector #v[true, false] = #v[false, true] := by decide
example : andNot.evalVector #v[true, true] = #v[true, false] := by decide
example : andNot.size = 2 := rfl
example : andNot.depth = 2 := by decide

private def choose : Circuit Language.booleanAlgebra 2 1 := .outputs ![1]

example : (choose.unroll 2).evalVector #v[false, true, false] = #v[false] := by decide
example : (choose.unroll 2).evalVector #v[false, false, true] = #v[true] := by decide
example : (choose.unroll 2).size = 0 := by simp [choose]

end Boolean

-- One symbol at every arity checks that the core does not assume bounded fan-in.
private inductive SumFunc : ℕ → Type
  | sum (n : ℕ) : SumFunc n

private def sumLanguage : Language := ⟨SumFunc, fun _ => Empty⟩
  deriving IsAlgebraic

private instance : sumLanguage.Structure ℕ where
  funMap | .sum _, x => ∑ i, x i

private def sumFour : Circuit sumLanguage 4 1 := .ofGate (.sum 4) id

example : sumFour.evalVector #v[1, 2, 3, 4] = #v[10] := by decide
example : sumFour.FanInAtMost 4 := by decide
example : ¬sumFour.FanInAtMost 3 := by decide
example : sumFour.depth = 1 := by decide

-- Nullary operations also compile from terms without a nonempty input context.
example : (Circuit.ofTerm (Term.func (.sum 0) Fin.elim0 :
    sumLanguage.Term (Fin 0))).evalVector #v[] = #v[0] := by decide

-- A gate basis can be interpreted differently before and after compilation.
private inductive BinaryFunc : ℕ → Type
  | binary : BinaryFunc 2

private def andLanguage : Language := ⟨BinaryFunc, fun _ => Empty⟩
  deriving IsAlgebraic

private def nandLanguage : Language := ⟨BinaryFunc, fun _ => Empty⟩
  deriving IsAlgebraic

private def andOps : ∀ {k}, andLanguage.Functions k → (Fin k → Bool) → Bool
  | _, .binary, x => x 0 && x 1

private def nandOps : ∀ {k}, nandLanguage.Functions k → (Fin k → Bool) → Bool
  | _, .binary, x => !(x 0 && x 1)

private def andAsNand : ∀ {k}, andLanguage.Functions k → Circuit nandLanguage k 1
  | _, .binary => .gate .binary ![0, 1] (.gate .binary ![2, 2] (.outputs ![3]))

private theorem andAsNand_correct {k} (op : andLanguage.Functions k) (x : Fin k → Bool) :
    (andAsNand op).evalWith nandOps x 0 = andOps op x := by
  cases op
  simp [andAsNand, Circuit.evalWith, nandOps, andOps, Function.comp_def, Fin.snoc]

private def sharedAnd : Circuit andLanguage 2 2 :=
  .gate .binary ![0, 1] (.gate .binary ![2, 2] (.outputs ![3, 2]))

example : (sharedAnd.compile andAsNand).size = 4 := by decide

example : (sharedAnd.compile andAsNand).depth ≤ 2 * sharedAnd.depth := by
  apply Circuit.depth_compile_le
  intro k op
  cases op
  decide

example (x : Fin 2 → Bool) :
    (sharedAnd.compile andAsNand).evalWith nandOps x = sharedAnd.evalWith andOps x :=
  sharedAnd.evalWith_compile andAsNand andOps nandOps andAsNand_correct x

-- Empty circuits do not require an inhabited value type.
private instance : Language.empty.Structure Empty where
  funMap f := Empty.elim f

example : (Circuit.id Language.empty 0).evalVector (#v[] : Vector Empty 0) = #v[] := rfl

end Complexity.CircuitTest
