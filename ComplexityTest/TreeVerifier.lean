/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Problems.CircuitSAT.Membership

open Complexity TreeProgram TreeProgram.Source
open TreeProgram.Source.Internal (HasProgramInO)

namespace Complexity.TreeVerifierTest

/-! ## Reading bit strings as trees -/

-- A prefix code gives its tree; other strings give some tree, here a leaf.
example (t : Tree) : BitList.toTree (BitList.encodeTree t) = t := by simp

example : BitList.toTree [true, false, true, false, false] = .pair .nil (.pair .nil .nil) := rfl

example : BitList.toTree [true, false] = .nil := rfl

-- Guards that the registered program of `BitList.toTree` gives memberships in `FP`, with the
-- size of its output known to `dominated` (`BitList.size_toTree_le`).
example : (fun x : ℕ × List Bool => (x.1, BitList.toTree x.2)) ∈ FP .sizeCostTree := by
  model_fun_prop

/-! ## Fuel -/

-- A quadratic bound in the input code size is exceeded by polynomial-time fuel.
example : ∃ fuel : List Bool → List Unit, fuel ∈ FP .sizeCostTree ∧
    ∀ xs, ⌜xs⌝ₜ.size ^ 2 ≤ (fuel xs).length :=
  TreeMachine.exists_fuel_mem_fp _ (IsPoly.refl.pow 2)

/-! ## Recognizing codes -/

-- The recognizer of natural-number codes accepts the binary digits of `6`, and rejects a final
-- `false` and an element that is not the code of a Boolean. The digits are written out, so that
-- `decide` does not reduce `Nat.bits`.
example : Tree.isNatCode ⌜[false, true, true]⌝ₜ = true := by decide

example : Tree.isNatCode ⌜[false, true, true, false]⌝ₜ = false := by decide

example : Tree.isNatCode (.pair (.pair (.pair .nil .nil) .nil) .nil) = false := by decide

-- Zero has the empty list of digits; a single `false` is a noncanonical code of zero.
example : Tree.isNatCode ⌜([] : List Bool)⌝ₜ = true := by decide

example : Tree.isNatCode ⌜[false]⌝ₜ = false := by decide

-- Guards a match on raw trees through `Tree.caseView`.
example : (fun t : Tree => match t with | .nil => (.nil : Tree) | .pair a _ => a) ∈
    FP .sizeCostTree := by
  model_fun_prop

-- Records a limit (plan W92): checking the trees of a spine by `List.all` leaves the peak open, as
-- the largest code among the trees of the spine, a computed list, is not bounded by `dominated`;
-- over a list given as input it is. `Tree.isNatCode` and `dom_decode_list_mem_p` check by folds
-- instead. If this starts to succeed, the checks can be written with `List.all`.
attribute [local program] Tree.hasProgramIn_isBoolCode in
/--
error: unsolved goals
case peak
-/
#guard_msgs (substring := true) in
example := (by source_fun_prop : HasProgramInO (fun t : Tree => t.spine.all Tree.isBoolCode) _
  (fun t => ⌜t⌝ₜ.size) (fun t => ⌜t⌝ₜ.size))

-- Guards the composition of the recognizers, as the witnesses of `k`-SAT ask for, and nested.
example : (fun t : Tree => (decode (List ℕ) t).Dom) ∈ P .sizeCostTree :=
  TreeMachine.dom_decode_list_mem_p TreeMachine.dom_decode_nat_mem_p

example : (fun t : Tree => (decode (List (List ℕ)) t).Dom) ∈ P .sizeCostTree :=
  TreeMachine.dom_decode_list_mem_p (TreeMachine.dom_decode_list_mem_p
    TreeMachine.dom_decode_nat_mem_p)

/-! ## Guard and verifiers -/

/-- Equality of natural numbers, decided by the translation. -/
theorem eq_mem_p : (fun x : ℕ × ℕ => x.2 = x.1) ∈ P .sizeCostTree :=
  P.of_decides (f := fun x : ℕ × ℕ => x.2 == x.1) (by model_fun_prop) fun _ => beq_iff_eq

-- Guards `p_guard`: the relation on trees holds only at codes of the witness type.
example : (fun x : ℕ × Tree => ∃ w : ℕ, ⌜w⌝ₜ = x.2 ∧ w = x.1) ∈ P .sizeCostTree :=
  TreeMachine.p_guard TreeMachine.dom_decode_nat_mem_p eq_mem_p

-- Guards the use of `nstack_of_tree_verifier`: the relation decided through the translation, the
-- bound by `dominated`, and a leaf as the witness.
example : (fun xs : List Bool => ∃ t : Tree, t.size ≤ xs.length + 1) ∈ NP .nstack :=
  nstack_of_tree_verifier (R := fun _ => True) (P.of_decides (f := fun _ => true)
    (by model_fun_prop) fun _ => by simp) (fun xs => xs.length + 1) (by dominated)
    (fun xs t _ => ⟨.nil, by simp⟩) fun xs _ => ⟨.nil, by simp, trivial⟩

-- Guards `NP.of_verifier` at a witness type other than lists; the relation, implicit, is read off
-- the membership `eq_mem_p`.
example : (fun n : ℕ => ∃ m : ℕ, m = n) ∈ NP .ntm :=
  NP.of_verifier TreeMachine.dom_decode_nat_mem_p eq_mem_p (fun n => ⌜n⌝ₜ.size) .refl
    (fun _ m h => ⟨m, h⟩) fun _ ⟨m, h⟩ => ⟨m, h ▸ le_rfl, h⟩

/-! ## Satisfiability -/

example (k : ℕ) : KSAT k ∈ NP .ntm := KSAT.mem_np k

example : CircuitSAT ∈ NP .ntm := CircuitSAT.mem_np

-- Guards that the memberships use no axiom beyond the standard ones.
/-- info: 'Complexity.KSAT.mem_np' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KSAT.mem_np

/--
info: 'Complexity.CircuitSAT.mem_np' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CircuitSAT.mem_np

end Complexity.TreeVerifierTest
