/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Primitives

noncomputable section

open Complexity TreeProgram.Source
open TreeProgram.Source.Internal (HasProgramInO)

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

example := (by source_fun_prop : HasProgramInO reverseByCases _ _ _)

-- The source equation stays an ordinary mathematical goal.
example : HasProgramInO (List.reverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop via reverseByCases
  case source_eq => funext xs; cases xs <;> simp [reverseByCases]

example : HasProgramInO (userReverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop via List.reverse
  case source_eq => exact userReverse_eq

section
attribute [local program] userReverse_eq

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgramInO
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => userReverse xs) _ _ _)
end

-- A local choice does not leak outside its section.
example : True := by
  fail_if_success
    have := (by source_fun_prop : HasProgramInO (userReverse (α := Bool)) _ _ _)
  trivial

def retain (xs : List Bool) := xs

theorem hasProgramIn_retainSlow :
    HasProgramIn retain hole(⊢ program) IsO(fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size)
    IsO(fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  abstract_hole program using programRetainSlow
  fill_hole program in source_fun_prop via (fun xs : List Bool => xs.reverse.reverse)
  case source_eq => funext xs; simp [retain]

-- The source equation does not optimize away the expressly selected program.
example : programRetainSlow = fun v => List.Code.reverse v >>= List.Code.reverse := rfl

section
@[local program] theorem retain_eq : retain = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [retain]

example := (by source_fun_prop : HasProgramInO retain programRetainSlow _ _)
end

example := (by source_fun_prop : HasProgramInO retain (fun v => pure v) _ _)

-- Source automation leaves unrelated proof goals alone.
example : HasProgramInO (userReverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) ∧ True := by
  constructor
  · fill_hole program in source_fun_prop via List.reverse
    case source_eq => exact userReverse_eq
  · trivial

namespace ReverseByCases

def userReverse {α : Type*} (xs : List α) := match xs with
  | [] => []
  | x :: xs => xs.reverse ++ [x]

theorem reverse_eq {α : Type*} : List.reverse (α := α) = userReverse := by
  funext xs
  cases xs <;> simp [userReverse]

-- Records that a function the library selects a program for gets no second one, also in a scope of
-- its own: another program is chosen at a call, with a local hypothesis or `via`. If this starts
-- to succeed, two selected programs of one function are active together.
/--
error: `program` already has a selected implementation of List.reverse: List.hasProgramIn_reverse; choose another one at a call with a local hypothesis or `via`
-/
#guard_msgs in
attribute [scoped program] reverse_eq

end ReverseByCases

-- The chosen interpretation states its own growth.
theorem hasProgramIn_customReverse {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.reverse (α := α)) hole(⊢ program)
      IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programCustomReverse
  fill_hole program in source_fun_prop via ReverseByCases.userReverse
  case source_eq => exact ReverseByCases.reverse_eq

-- A local implementation stated with `HasProgramIn` chooses it at a call.
example {α : Type*} [UniqueEncoding Tree α]
    (_h : HasProgramIn (List.reverse (α := α)) programCustomReverse IsO(fun xs => ⌜xs⌝ₜ.size)
      IsO(fun xs => ⌜xs⌝ₜ.size)) :=
  (by source_fun_prop : HasProgramInO (List.reverse (α := α)) programCustomReverse _ _)

example := (by source_fun_prop : HasProgramInO (List.reverse (α := Bool)) List.Code.reverse _ _)

-- A local function implemented by a `HasProgramIn` hypothesis is composed as with a `HasProgramInO`
-- one: within `IsO` with the stated growths.
example {h : List Bool → List Bool}
    {program : TreeProgram.Value → TreeProgram.Code TreeProgram.Value}
    (_h : HasProgramIn h program IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size)) :
    HasProgramIn (fun xs : List Bool => h xs.reverse) hole(program ⊢ composed)
      IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole composed in source_fun_prop

-- Under a polynomial growth the composition uses the chosen growths `h.time`, `h.peak`; the
-- polynomial goal follows when the size of the intermediate value is known, here that of a
-- reversal.
example {h : List Bool → List Bool}
    {program : TreeProgram.Value → TreeProgram.Code TreeProgram.Value}
    (_h : HasProgramIn h program (IsPoly fun xs => ⌜xs⌝ₜ.size) (IsPoly fun xs => ⌜xs⌝ₜ.size)) :
    HasProgramIn (fun xs : List Bool => h xs.reverse) hole(program ⊢ composed)
      (IsPoly fun xs => ⌜xs⌝ₜ.size) (IsPoly fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole composed in source_fun_prop

-- Records a limit: the size of a value computed by another polynomial implementation is not
-- derived, so `IsPoly (⌜·⌝ₜ.size) fun x => g.time x + h.time (g x)` is left. When this starts to
-- succeed, the size of an intermediate value follows from the peak of its implementation.
example {g h : List Bool → List Bool}
    {pg ph : TreeProgram.Value → TreeProgram.Code TreeProgram.Value}
    (_g : HasProgramIn g pg (IsPoly fun xs => ⌜xs⌝ₜ.size) (IsPoly fun xs => ⌜xs⌝ₜ.size))
    (_h : HasProgramIn h ph (IsPoly fun xs => ⌜xs⌝ₜ.size) (IsPoly fun xs => ⌜xs⌝ₜ.size)) :
    True := by
  fail_if_success
    have : HasProgramIn (fun xs : List Bool => h (g xs)) hole(pg, ph ⊢ composed)
        (IsPoly fun xs => ⌜xs⌝ₜ.size) (IsPoly fun xs => ⌜xs⌝ₜ.size) := by
      fill_hole composed in source_fun_prop
      done
  trivial

def chosenReverse {α : Type*} : List α → List α := List.reverse

-- The program attribute saves the implementation of an equality's right-hand side for ordinary
-- nested calls.
@[program] theorem chosenReverse_eq {α : Type*} :
    chosenReverse (α := α) = ReverseByCases.userReverse := by
  rw [← ReverseByCases.reverse_eq]; rfl

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgramInO
    (fun x : List α × Option (List α) =>
      match x.2 with | none => x.1 | some xs => chosenReverse xs) _ _ _)

attribute [program] userReverse_eq

namespace Scoped

def custom (xs : List Bool) := xs
@[scoped program] theorem custom_eq : custom = (fun xs : List Bool => xs.reverse.reverse) := by
  funext xs; simp [custom]

end Scoped

example := (by source_fun_prop : HasProgramInO Scoped.custom (fun v => pure v) _ _)

open scoped Scoped in
example := (by source_fun_prop : HasProgramInO Scoped.custom programRetainSlow _ _)

section
@[local program] theorem identity_eq :
    (id : List Bool → List Bool) = (fun xs => xs.reverse.reverse) := by funext xs; simp

example := (by source_fun_prop : HasProgramInO (id : List Bool → List Bool) programRetainSlow _ _)
end

-- An unsupported replacement does not fall back to the supported original source.
example : True := by
  fail_if_success
    have := (by source_fun_prop via (fun xs : List Nat => xs.map Nat.factorial) :
      HasProgramInO (List.reverse (α := Nat)) _ (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size))
  trivial

theorem conditionalChoice (h : False) : (id : List Bool → List Bool) = List.reverse :=
  False.elim h

/-- error: `program` needs an unconditional function equality; use a local `via` proof for a replacement depending on a hypothesis -/
#guard_msgs in
attribute [program] conditionalChoice

def unregisteredReverse : List Bool → List Bool
  | [] => []
  | x :: xs => unregisteredReverse xs ++ [x]

theorem unsupportedChoice : (List.reverse : List Bool → List Bool) = unregisteredReverse := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [unregisteredReverse, ← ih]

/-- error: source translation: `ComplexityTest.SourceTranslation.Guidance.unregisteredReverse` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[program]`) -/
#guard_msgs in
attribute [program] unsupportedChoice

open Lean Elab Command in
run_elab do
  let env ← getEnv
  if env.constants.fold (init := false) (fun found name _ => found ||
      (`ComplexityTest.SourceTranslation.Guidance.unsupportedChoice.sourceProgram).isPrefixOf name) then
    throwError "a failed source registration left a partial implementation"

end ComplexityTest.SourceTranslation.Guidance
