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

example := (by source_fun_prop : Implementation reverseByCases _ _)

-- The source equation stays an ordinary mathematical goal.
example : Implementation (List.reverse (α := Bool)) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop via reverseByCases
  case source_eq => funext xs; cases xs <;> simp [reverseByCases]
  all_goals dominated

example : Implementation (userReverse (α := Bool)) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop via List.reverse
  case source_eq => exact userReverse_eq

section
attribute [local source] userReverse_eq

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : Implementation
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => userReverse xs) _ _)
end

-- A local choice does not leak outside its section.
example : True := by
  fail_if_success
    have := (by source_fun_prop : Implementation (userReverse (α := Bool)) _ _)
  trivial

def retain (xs : List Bool) := xs

def retainSlow : Implementation retain (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size)
    (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  source_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
  case source_eq => funext xs; simp [retain]

-- The source equation does not optimize away the expressly selected program.
example : retainSlow.program = (Implementation.reverse.comp
    (Implementation.reverse (α := Bool))).program := rfl

section
@[local source] theorem retain_eq : retain = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [retain]

example : (by source_fun_prop : Implementation retain _ _).program = retainSlow.program := rfl
end

example : (by source_fun_prop : Implementation retain _ _).program =
    (Implementation.identity (α := List Bool)).program := rfl

-- Source automation leaves unrelated proof goals alone.
example : Nonempty (Implementation (userReverse (α := Bool)) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size)) ∧ True := by
  constructor
  · refine ⟨?_⟩
    source_fun_prop via List.reverse
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
def customReverseImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.reverse (α := α)) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop using ReverseByCases
  all_goals dominated

open scoped ReverseByCases in
example {α : Type*} [UniqueEncoding Tree α] :
    (by source_fun_prop : Implementation (List.reverse (α := α)) _ _).program =
      (customReverseImplementation (α := α)).program := rfl

example : (by source_fun_prop : Implementation (List.reverse (α := Bool)) _ _).program =
    (Implementation.reverse (α := Bool)).program := rfl

example : Implementation (userReverse (α := Bool)) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop using ReverseByCases via List.reverse
  case source_eq => exact userReverse_eq
  all_goals
    apply Dominated.of_le_mul 4
    rintro (_ | ⟨x, xs⟩)
    · simp
    · have := size_encode_list xs
      simp
      omega

def chosenReverse {α : Type*} : List α → List α := List.reverse

-- The source attribute saves the chosen implementation for ordinary nested calls.
@[source using ReverseByCases] theorem chosenReverse_eq {α : Type*} :
    chosenReverse (α := α) = List.reverse := rfl

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : Implementation
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => chosenReverse xs) _ _)

attribute [source] userReverse_eq

namespace Scoped

def custom (xs : List Bool) := xs
@[scoped source] theorem custom_eq : custom = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [custom]

end Scoped

example : (by source_fun_prop : Implementation Scoped.custom _ _).program =
    (Implementation.identity (α := List Bool)).program := rfl

open scoped Scoped in
example : (by source_fun_prop : Implementation Scoped.custom _ _).program =
    retainSlow.program := rfl

section
@[local source] theorem identity_eq :
    (id : List Bool → List Bool) = (fun xs => xs.reverse.reverse) := by funext xs; simp

example : (by source_fun_prop : Implementation (id : List Bool → List Bool) _ _).program =
    retainSlow.program := rfl
end

-- An unsupported replacement does not fall back to the supported original source.
example : True := by
  fail_if_success
    have : Implementation (List.reverse (α := Nat)) (fun xs => ⌜xs⌝ₜ.size)
        (fun xs => ⌜xs⌝ₜ.size) := by
      source_fun_prop via (fun xs : List Nat => xs.map Nat.factorial)
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
      (`ComplexityTest.SourceTranslation.Guidance.unsupportedChoice.sourceImplementation).isPrefixOf name) then
    throwError "a failed source registration left a partial implementation"

end ComplexityTest.SourceTranslation.Guidance
