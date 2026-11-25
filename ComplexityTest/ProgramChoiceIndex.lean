/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Program.Traverse
import Complexity.Resources.StackMachine.Program

set_option experimental.vcgen true

open Complexity Std.WP BinaryChoice
open Complexity.StackMachine (Cfg)
open Complexity.StackMachine.Program

/-!
# Guessing an index

A binary-choice stack program accepts the inputs with a bit `true` by guessing its position. Under
`MonadQuant.any` the guess depends on the state, through a body lemma for each loop index; the
`MonadQuant.all` and `MonadQuant.any` specifications give a nondeterministic decision on
`TimeSpaceModel.nstack`. The entry itself is stated for any choice shape.
-/

namespace ProgramChoiceIndexTest

/-- At an input symbol, guess whether this is the position, mark stack `0` when the guess falls on
a `true`, and advance; at the right boundary, stop. -/
def scanBody : StackMachine.Program BinaryChoice (Fin 1) Bool Bool := do
  let x ← readInput
  if x.isSome then
    let c ← choose coin
    if c && x == some true then
      push 0 true
      moveInput 1
      pure false
    else
      moveInput 1
      pure false
  else pure true

/-- Emit the code of a Boolean. -/
def emitBool (v : Bool) : StackMachine.Program BinaryChoice (Fin 1) Bool Unit :=
  if v then do emit true; emit false; emit false else emit false

/-- Scan the input guessing the position of a `true`, then emit whether a mark was made. -/
def guessIndex : StackMachine.Program BinaryChoice (Fin 1) Bool Unit := do
  repeatUntil scanBody
  let top ← read 0
  emitBool top.isSome

-- Guards the `MonadQuant.all` specification of a loop with a choice in its body: the registered
-- rule of `choose` fires, and the loop exit leaves the continuation as a raw `wp` for a second
-- `vcgen`.
theorem guessIndex_all (xs : List Bool) :
    Triple (guessIndex.verifyWith Multiset .all (semantics xs.toArray))
      (fun s b ↦ s = Cfg.init (Fin 1) xs ∧ b = 5 * xs.length + 6)
      (fun _ s _ ↦ ∃ v : Bool, s.output = ⌜v⌝₂.toList.toArray ∧ (v = true → true ∈ xs)) () := by
  unfold guessIndex repeatUntil scanBody moveInput emitBool emit
  vcgen invariants
  | inv1 => fun s b ↦ ∃ j ≤ xs.length, s.inputPos.val = j + 1 ∧ s.output = #[] ∧
      (s.stacks 0 ≠ [] → true ∈ xs) ∧ 5 * (xs.length - j) + 6 ≤ b
  case vc1 => simp_all
  case vc2 =>
    obtain ⟨j, -, -, -, -, hb⟩ := ‹∃ j ≤ _, _›
    omega
  all_goals obtain ⟨_, ⟨j, hj, hpos, hout, hst, hb⟩, rfl⟩ := ‹∃ t, _›
  case' vc9 =>
    simp only [ite_true]
    vcgen
  all_goals
    cases_type* And
    subst_vars
    simp only [semantics_act, idle_apply] at *
  all_goals first | omega | (try simp_all [idle, Input.movePos, StackMachine.Op.apply])
  all_goals (try omega)
  · decide
  · exact Or.inl (by decide)
  · exact ⟨List.mem_iff_getElem.2 ⟨j, ‹_›, ‹_ ∧ _›.2⟩, by omega⟩

/-! ## The `MonadQuant.any` specification -/

-- Guards that under `MonadQuant.any` the chosen value may depend on the loop index: the body lemma
-- is stated for each index `j` and gives `spec_choose_any` the value `decide (j = i)`.
/-- The body at the `j`-th symbol, choosing whether `j = i`. -/
theorem scanBody_any_step (xs : List Bool) (i j : ℕ) (hi : i < xs.length) (hxi : xs[i] = true)
    (hj : j < xs.length) :
    Triple (scanBody.verifyWith Multiset .any (semantics xs.toArray))
      (fun s b ↦ s.inputPos.val = j + 1 ∧ s.output = #[] ∧ (i < j → s.stacks 0 ≠ []) ∧
        5 * (xs.length - j) + 6 ≤ b + 1)
      (fun r s b ↦ r = false ∧ s.inputPos.val = j + 1 + 1 ∧ s.output = #[] ∧
        (i < j + 1 → s.stacks 0 ≠ []) ∧ 5 * (xs.length - (j + 1)) + 6 ≤ b) () := by
  unfold scanBody moveInput
  vcgen [spec_choose_any coin (decide (j = i)) (mem_returns_coin _)]
  all_goals
    cases_type* And
    subst_vars
  all_goals first | omega | (try simp_all [idle, Input.movePos, StackMachine.Op.apply])
  all_goals (try omega)
  exact ⟨by omega, fun h ↦ ‹i < j → _› (by omega), by omega⟩

-- Records that a choice in a branch that the precondition excludes still needs a rule under
-- `MonadQuant.any`, since `vcgen` enters both branches; any value serves.
/-- The body at the end of the input stops. -/
theorem scanBody_any_done (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    Triple (scanBody.verifyWith Multiset .any (semantics xs.toArray))
      (fun s b ↦ s.inputPos.val = xs.length + 1 ∧ s.output = #[] ∧
        (i < xs.length → s.stacks 0 ≠ []) ∧ 5 * (xs.length - xs.length) + 6 ≤ b + 1)
      (fun r s b ↦ r = true ∧ s.output = #[] ∧ s.stacks 0 ≠ [] ∧ 4 ≤ b) () := by
  unfold scanBody moveInput
  vcgen [spec_choose_any coin true (mem_returns_coin _)]
  all_goals
    cases_type* And
    subst_vars
  all_goals (try simp_all); all_goals omega

-- Guards the `MonadQuant.any` specification from a body lemma for each loop index, through the
-- counted loop rule: the chosen value is a fixed term in the body lemma, and the loop exit
-- continues directly.
theorem guessIndex_any (xs : List Bool) (i : ℕ) (hi : i < xs.length) (hxi : xs[i] = true) :
    Triple (guessIndex.verifyWith Multiset .any (semantics xs.toArray))
      (fun s b ↦ s = Cfg.init (Fin 1) xs ∧ b = 5 * xs.length + 6)
      (fun _ s _ ↦ s.output = ⌜true⌝₂.toList.toArray) () := by
  have hloop := Program.spec_repeatUntilWith_count_of_invariant idle scanBody
    (semantics xs.toArray)
    (fun j s b ↦ s.inputPos.val = j + 1 ∧ s.output = #[] ∧ (i < j → s.stacks 0 ≠ []) ∧
      5 * (xs.length - j) + 6 ≤ b)
    (fun s b ↦ s.output = #[] ∧ s.stacks 0 ≠ [] ∧ 4 ≤ b) xs.length
    (by simp) (by intros; omega) (fun j hj ↦ scanBody_any_step xs i j hi hxi hj)
    (scanBody_any_done xs i hi)
  unfold guessIndex repeatUntil emitBool emit
  vcgen [hloop]
  all_goals
    cases_type* And
    subst_vars
  all_goals first | omega | (try simp_all [idle])
  decide

-- Guards the passage from the two specifications to a nondeterministic decision on the stack
-- model, through `nDecidableWithinByCode_of_spec`.
theorem guessIndex_nDecidable :
    TimeSpaceModel.nstack.NDecidableWithinByCode (fun r : RawWord Bool ↦ true ∈ r.toList)
      (fun _ r ↦ 5 * r.length + 6) (fun _ r ↦ Fintype.card (Fin 1) * (5 * r.length + 6)) := by
  refine nDecidableWithinByCode_of_spec guessIndex _ (fun a r ha ↦ ?_) fun a r ha hp ↦ ?_
  · obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
    exact guessIndex_all _
  · obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.1 hp
    exact guessIndex_any _ i hi hxi

-- Guards that the entry is stated for any choice shape: for choices given as multisets of outcomes
-- all its instance arguments are found, and the model is
-- `TimeSpaceModel.stackWith Multiset Multiset`.
example {p : RawWord Bool → Prop} (prog : StackMachine.Program Multiset (Fin 1) Bool Unit)
    (t : RawWord Bool → RawWord Bool → ℕ)
    (hall : ∀ a r, a ∈ decode (RawWord Bool) r →
      Triple (prog.verifyWith Multiset .all (semantics r.toList.toArray))
        (fun s b ↦ s = Cfg.init (Fin 1) r.toList ∧ b = t a r)
        (fun _ s _ ↦ ∃ v : Bool, s.output = ⌜v⌝₂.toList.toArray ∧ (v = true → p a)) ())
    (hany : ∀ a r, a ∈ decode (RawWord Bool) r → p a →
      Triple (prog.verifyWith Multiset .any (semantics r.toList.toArray))
        (fun s b ↦ s = Cfg.init (Fin 1) r.toList ∧ b = t a r)
        (fun _ s _ ↦ s.output = ⌜true⌝₂.toList.toArray) ()) :
    (TimeSpaceModel.stackWith Multiset Multiset).NDecidableWithinByCode p t
      (fun a r ↦ Fintype.card (Fin 1) * t a r) :=
  nDecidableWithinByCode_of_spec prog t hall hany

/-! ## Records of limits of `vcgen` met by the guess of a bit string -/

/-- Push `true` when `c` holds, then `false`. -/
def pushIf (c : Bool) : StackMachine.Program Id (Fin 1) Bool Unit := do
  if c then push 0 true else pure ()
  push 0 false

-- Records a limit: an `if` statement followed by further statements elaborates to a join point
-- `have __do_jp := …`, for which `vcgen` has no rule, with or without an `else`. `recordBit`
-- branches inside the tree action, `build (if x then .pair tmp tmp tmp else .nop)`, rather than on
-- a statement; this form was chosen for the limit while `spec_recordBit` was proved by `vcgen`.
-- `spec_recordBit` now composes the four `spec_build` steps by hand and does not meet the limit.
-- If this starts to succeed, a program branching on a statement can be proved by `vcgen`.
example (c : Bool) (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple ((pushIf c).verify (semantics xs)) (fun s b ↦ s = s₀ ∧ b = 3) (fun _ _ _ ↦ True)
      () := by
  unfold pushIf
  fail_if_success vcgen
  cases c
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    vcgen
    all_goals simp_all

/-- `pushIf` without the `else`. -/
def pushIfThen (c : Bool) : StackMachine.Program Id (Fin 1) Bool Unit := do
  if c then push 0 true
  push 0 false

-- Records the same limit for an `if` statement without an `else`.
example (c : Bool) (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple ((pushIfThen c).verify (semantics xs)) (fun s b ↦ s = s₀ ∧ b = 3) (fun _ _ _ ↦ True)
      () := by
  unfold pushIfThen
  fail_if_success vcgen
  cases c
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    vcgen
    all_goals simp_all

end ProgramChoiceIndexTest
