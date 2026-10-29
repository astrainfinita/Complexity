/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Translation

noncomputable section

open Complexity TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Guidance

def userReverse {α : Type*} : List α → List α
  | [] => []
  | x :: xs => userReverse xs ++ [x]

theorem userReverse_eq {α : Type*} : userReverse (α := α) = List.reverse := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [userReverse, ih]

private def reverseByCases (xs : List Bool) := match xs with
  | [] => []
  | x :: xs => (x :: xs).reverse

example := (by source_fun_prop : HasProgram reverseByCases _ _ _)

-- The source equation stays an ordinary mathematical goal.
example : HasProgram (List.reverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop via reverseByCases
  case source_eq => funext xs; cases xs <;> simp [reverseByCases]

example : HasProgram (userReverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop via List.reverse
  case source_eq => exact userReverse_eq

section
attribute [local source] userReverse_eq

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgram
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => userReverse xs) _ _ _)
end

-- A local choice does not leak outside its section.
example : True := by
  fail_if_success
    have := (by source_fun_prop : HasProgram (userReverse (α := Bool)) _ _ _)
  trivial

def retain (xs : List Bool) := xs

theorem hasProgram_retainSlow :
    HasProgram retain hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size)
    (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  abstract_hole program using programRetainSlow
  fill_hole program in source_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
  case source_eq => funext xs; simp [retain]

-- The source equation does not optimize away the expressly selected program.
example : programRetainSlow = fun v => List.Code.reverse v >>= List.Code.reverse := rfl

section
@[local source] theorem retain_eq : retain = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [retain]

example := (by source_fun_prop : HasProgram retain programRetainSlow _ _)
end

example := (by source_fun_prop : HasProgram retain (fun v => pure v) _ _)

-- Source automation leaves unrelated proof goals alone.
example : HasProgram (userReverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) ∧ True := by
  constructor
  · fill_hole program in source_fun_prop via List.reverse
    case source_eq => exact userReverse_eq
  · trivial

namespace ReverseByCases

def userReverse {α : Type*} (xs : List α) := match xs with
  | [] => []
  | x :: xs => xs.reverse ++ [x]

@[scoped source] theorem reverse_eq {α : Type*} :
    List.reverse (α := α) = userReverse := by
  funext xs
  cases xs <;> simp [userReverse]

end ReverseByCases

-- The selected interpretation states its own growth.
theorem hasProgram_customReverse {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (List.reverse (α := α)) hole(⊢ program)
      (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programCustomReverse
  fill_hole program in source_fun_prop using ReverseByCases

open scoped ReverseByCases in
example {α : Type*} [UniqueEncoding Tree α] :=
  (by source_fun_prop : HasProgram (List.reverse (α := α)) programCustomReverse _ _)

example := (by source_fun_prop : HasProgram (List.reverse (α := Bool)) List.Code.reverse _ _)

example : HasProgram (userReverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop using ReverseByCases via List.reverse
  case source_eq => exact userReverse_eq

def chosenReverse {α : Type*} : List α → List α := List.reverse

-- The source attribute saves the chosen implementation for ordinary nested calls.
@[source using ReverseByCases] theorem chosenReverse_eq {α : Type*} :
    chosenReverse (α := α) = List.reverse := rfl

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgram
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => chosenReverse xs) _ _ _)

attribute [source] userReverse_eq

namespace Scoped

def custom (xs : List Bool) := xs
@[scoped source] theorem custom_eq : custom = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [custom]

end Scoped

example := (by source_fun_prop : HasProgram Scoped.custom (fun v => pure v) _ _)

open scoped Scoped in
example := (by source_fun_prop : HasProgram Scoped.custom programRetainSlow _ _)

section
@[local source] theorem identity_eq :
    (id : List Bool → List Bool) = (fun xs => xs.reverse.reverse) := by funext xs; simp

example := (by source_fun_prop : HasProgram (id : List Bool → List Bool) programRetainSlow _ _)
end

-- An unsupported replacement does not fall back to the supported original source.
example : True := by
  fail_if_success
    have := (by source_fun_prop via (fun xs : List Nat => xs.map Nat.factorial) :
      HasProgram (List.reverse (α := Nat)) _ (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size))
  trivial

theorem conditionalChoice (h : False) : (id : List Bool → List Bool) = List.reverse :=
  False.elim h

/-- error: `source` needs an unconditional function equality; use a local `via` proof for a replacement depending on a hypothesis -/
#guard_msgs in
attribute [source] conditionalChoice

def unregisteredReverse : List Bool → List Bool
  | [] => []
  | x :: xs => unregisteredReverse xs ++ [x]

theorem unsupportedChoice : (List.reverse : List Bool → List Bool) = unregisteredReverse := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [unregisteredReverse, ← ih]

/-- error: source translation: `ComplexityTest.SourceTranslation.Guidance.unregisteredReverse` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`) -/
#guard_msgs in
attribute [source] unsupportedChoice

open Lean Elab Command in
run_elab do
  let env ← getEnv
  if env.constants.fold (init := false) (fun found name _ => found ||
      (`ComplexityTest.SourceTranslation.Guidance.unsupportedChoice.sourceProgram).isPrefixOf name) then
    throwError "a failed source registration left a partial implementation"

end ComplexityTest.SourceTranslation.Guidance
