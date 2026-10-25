/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.Hole
import Mathlib.Tactic.Linter.UnusedTactic

/-! Holes in statements: filling, abstraction, display, and what does not fill a hole. -/

@[expose] public section

namespace ComplexityTest.Hole

-- A hole without context is a constant of the statement.
/--
trace: n : Nat
⊢ hole(⊢ five) + n = 5 + n
---
trace: n : Nat
⊢ 5 + n = 5 + n
-/
#guard_msgs in
theorem const (n : Nat) : hole(⊢ five) + n = 5 + n := by
  trace_state
  fill_hole five := 5
  trace_state
  rfl

/-- info: ComplexityTest.Hole.const (n : Nat) : 5 + n = 5 + n -/
#guard_msgs in
#check const

-- The context is the statement's: the goal renaming or replacing the variable does not matter.
/--
trace: ⊢ ∀ (n : Nat), hole(n ⊢ twice) = n + n
---
trace: k : Nat
⊢ hole(n := k ⊢ twice) = k + k
---
trace: k : Nat
⊢ k + k = k + k
-/
#guard_msgs in
theorem renamed : ∀ n : Nat, hole(n ⊢ twice) = n + n := by
  trace_state
  intro k
  trace_state
  fail_if_success fill_hole twice := k + k
  fill_hole twice := n + n
  trace_state
  rfl

/-- info: ComplexityTest.Hole.renamed (n : Nat) : n + n = n + n -/
#guard_msgs in
#check renamed

/--
trace: case zero
⊢ hole(n := 0 ⊢ double) = 2 * 0
-/
#guard_msgs in
theorem split (n : Nat) : hole(n ⊢ double) = 2 * n := by
  cases n with
  | zero => trace_state; fill_hole double := 2 * n; rfl
  | succ k => rfl

-- Unification does not fill a hole: Lean runs no unification at the depth of holes.
example : hole(⊢ seven) = 7 := by
  fail_if_success exact rfl
  fail_if_success rfl
  fail_if_success decide
  fail_if_success simp
  fill_hole seven := 7
  rfl

-- `?eight` is a new metavariable, not the hole: holes have inaccessible names.
/--
trace: ⊢ hole(⊢ eight) = ?eight

case eight
⊢ Nat
-/
#guard_msgs in
example : ∃ k : Nat, hole(⊢ eight) = k := by
  refine ⟨?eight, ?_⟩
  rotate_left
  trace_state
  fill_hole eight := 8
  exact rfl

-- `fill_hole a in tac` lets unification in `tac` fill the hole.
theorem byRfl : ∀ n : Nat, hole(n ⊢ triple) = n + n + n := by
  intro k
  fill_hole triple in exact rfl

/-- info: ComplexityTest.Hole.byRfl (n : Nat) : n + n + n = n + n + n -/
#guard_msgs in
#check byRfl

-- A definition stands for the hole; it may be named before the hole is filled. A statement with
-- holes is elaborated before the next command, so the definition may have any name.
/--
trace: n : Nat
⊢ hole(n ⊢ quadruple) = 4 * n
---
trace: n : Nat
⊢ quadrupleDef n = 4 * n
-/
#guard_msgs in
theorem abstracted (n : Nat) : hole(n ⊢ quadruple) = 4 * n := by
  abstract_hole quadruple using quadrupleDef
  trace_state
  fill_hole quadruple := 4 * n
  trace_state
  rfl

/--
info: @[expose] def ComplexityTest.Hole.quadrupleDef : Nat → Nat :=
fun n => 4 * n
-/
#guard_msgs in
#print quadrupleDef

theorem abstractedByRfl (n : Nat) : hole(n ⊢ quintuple) = 5 * n := by
  abstract_hole quintuple using _root_.ComplexityTest.quintupleDef
  fill_hole quintuple in rfl

/-- info: ComplexityTest.Hole.abstractedByRfl (n : Nat) : quintupleDef n = 5 * n -/
#guard_msgs in
#check abstractedByRfl

/-- trace: ⊢ sixDef = 6 -/
#guard_msgs in
theorem abstractedAfter : hole(⊢ six) = 6 := by
  fill_hole six := 6
  abstract_hole six using sixDef
  trace_state
  rfl

-- The definition is private with the statement.
private theorem abstractedPrivate : hole(⊢ nine) = 9 := by
  abstract_hole nine using nineDef
  fill_hole nine := 9
  rfl

/--
info: private def ComplexityTest.Hole.nineDef : Nat :=
9
-/
#guard_msgs in
#print nineDef

-- A hole in a proof is not one of its goals.
/-- trace: ⊢ hole(⊢ ten) = 10 -/
#guard_msgs in
example : True := by
  refine (fun (_ : hole(⊢ ten) = 10) => trivial) ?_
  trace_state
  fill_hole ten := 10
  rfl

-- Filling or naming a hole changes no goal, and is not an unused tactic.
/-- warning: Unused tactic linter: `skip` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false` -/
#guard_msgs in
set_option linter.unusedTactic true in
theorem linted : hole(⊢ twelve) = 12 := by
  fill_hole twelve := 12
  abstract_hole twelve using twelveDef
  skip
  rfl

/-! Errors. -/

/-- error: there is no hole `one` -/
#guard_msgs in
example : ∃ k : Nat, k = 1 := by
  refine ⟨?one, ?_⟩
  fill_hole one := 1

/--
error: Unknown identifier `m`

The value is written in the context of the hole `outside`, which consists of `n`.
-/
#guard_msgs in
example (m n : Nat) : hole(n ⊢ outside) = m + n := by
  fill_hole outside := m + n

/-- error: the hole `twiceFilled` is already filled -/
#guard_msgs in
example : hole(⊢ twiceFilled) = 1 := by
  fill_hole twiceFilled := 1
  fill_hole twiceFilled := 1

/-- error: the tactic did not fill the hole `notFilled` -/
#guard_msgs in
example : hole(⊢ notFilled) = 1 ∨ True := by
  fill_hole notFilled in exact Or.inr trivial

/--
error: the hole `pair` is only partly filled:
  (1, ?_)
-/
#guard_msgs in
example : hole(⊢ pair) = (1, 2) := by
  fill_hole pair in apply congrArg (Prod.mk 1)

/-- error: the hole `twiceAbstracted` is already abstracted -/
#guard_msgs in
example : hole(⊢ twiceAbstracted) = 1 := by
  abstract_hole twiceAbstracted using twiceAbstractedDef
  abstract_hole twiceAbstracted using twiceAbstractedDef'

/-- error: a non-private declaration `ComplexityTest.Hole.const` has already been declared -/
#guard_msgs in
example : hole(⊢ known) = 1 := by
  abstract_hole known using const

/-- error: the hole `abstractedOnly` is not filled -/
#guard_msgs in
example : hole(⊢ abstractedOnly) = 1 := by
  abstract_hole abstractedOnly using abstractedOnlyDef
  sorry

-- A hole no tactic is about is reported only by the kernel: Lean checks a statement for unfilled
-- parts before its proof.
/--
warning: declaration uses `sorry`
---
error: (kernel) declaration has metavariables 'ComplexityTest.Hole._example'
-/
#guard_msgs in
example : hole(⊢ unmentioned) = 1 := by
  sorry

-- A hole in the proof of a theorem without holes in its statement: the proof is elaborated in
-- parallel, and may only add declarations named after the theorem.
/--
error: cannot add declaration _private.ComplexityTest.Hole.0.ComplexityTest.Hole.elevenDef to environment as it is restricted to the prefix ComplexityTest.Hole.inProof
-/
#guard_msgs in
theorem inProof : True := by
  have : hole(⊢ eleven) = 11 := by
    abstract_hole eleven using elevenDef
    fill_hole eleven := 11
    rfl
  trivial

/-- error: the type of the hole `mentions` mentions `n`, which it does not list -/
#guard_msgs in
example (n : Nat) (i : Fin n) : hole(⊢ mentions) = i := by
  sorry

/-- error: the type of `i` mentions `n`, which must be listed before it -/
#guard_msgs in
example (n : Nat) (i : Fin n) : hole(i, n ⊢ order) = i := by
  sorry

/-- error: unknown variable `k` -/
#guard_msgs in
example (m : Nat) : hole(m, k ⊢ unknown) = m := by
  sorry

/-- error: `m` is listed twice -/
#guard_msgs in
example (m : Nat) : hole(m, m ⊢ repeated) = m := by
  sorry

/-- error: `m` is a `let` variable -/
#guard_msgs in
example : let m := 1; hole(m ⊢ letBound) = m := by
  sorry

/-- error: a hole lists variables; `x := t` appears only in goals -/
#guard_msgs in
example (m : Nat) : hole(m := 1 ⊢ assigned) = m := by
  sorry

/--
error: the type of the hole `untyped` is not known, expected type contains metavariables
  ?_
-/
#guard_msgs in
example : (fun _ => 1) hole(⊢ untyped) = 1 := by
  sorry

/--
error: there is already a hole `same`
---
error: (kernel) declaration has metavariables 'ComplexityTest.Hole._example'
-/
#guard_msgs in
example : (hole(⊢ same) : Nat) = (hole(⊢ same) : Nat) := by
  sorry

end ComplexityTest.Hole
