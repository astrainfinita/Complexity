/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.List
public import Complexity.Encoding.Nat

/-! # Binary counters in ordinary tree programs -/

@[expose] public section

open Complexity TreeProgram TreeProgram.Code

namespace Nat.Code

attribute [local simp] encode_prod encode_unit

/-- Move one low `true` bit into the zero prefix and refresh the carry test. -/
@[simps! build_snd_fst]
def succStep (rest zeros test : Var) : TreeProgram.Code Unit := do
  let r ← read rest
  write zeros (← Value.pair .nil (← read zeros))
  let next ← r.right
  write rest next
  write test (← next.left)

/-- Binary successor. Only the low carry prefix is traversed; the suffix is reused. -/
def succ (xs : Value) : TreeProgram.Code Value := do
  let rest ← newVar xs
  let zeros ← newVar .nil
  let test ← newVar (← (← read rest).left)
  whileNode test (succStep rest zeros test)
  let r ← read rest
  let one ← Value.pair .nil .nil
  let suffix ← one.pair (← r.right)
  List.Code.reverseAppend (← read zeros) suffix

private theorem succStep_bounded (n : ℕ) (s : ℕ → Tree) (r a : List Bool) (space : ℕ)
    (hr : s n = encode Tree (true :: r)) (ha : s (n + 1) = encode Tree a)
    (hs : (encode Tree (true :: r)).size + (encode Tree a).size ≤ space) :
    (succStep ⟨n⟩ ⟨n + 1⟩ ⟨n + 4⟩).Bounded (n + 5) s 13 space (fun _ t ↦
      t n = encode Tree r ∧ t (n + 1) = encode Tree (false :: a) ∧
      t (n + 4) = (encode Tree r).left ∧ ∀ j < n, t j = s j) := by
  have hleft := Tree.size_left_le (encode Tree r)
  simp +contextual (disch := omega) [succStep, hr, ha] at *
  omega

private theorem succLoop_bounded (n : ℕ) (s : ℕ → Tree) (bs : List Bool)
    (hr : s n = encode Tree bs) (ha : s (n + 1) = .nil)
    (ht : s (n + 4) = (encode Tree bs).left) :
    (whileNode ⟨n + 4⟩ (succStep ⟨n⟩ ⟨n + 1⟩ ⟨n + 4⟩)).Bounded (n + 5) s
      (15 * bs.length + 2) ((encode Tree bs).size + 1) (fun _ t ↦
        ∃ r a : List Bool, t n = encode Tree r ∧ t (n + 1) = encode Tree a ∧
          (encode Tree a).reverseAppend (.pair (encode Tree true) (encode Tree r).right) =
            encode Tree (BitList.increment bs) ∧
          (encode Tree r).size + (encode Tree a).size ≤ (encode Tree bs).size + 1 ∧
          a.length + r.length = bs.length ∧ ∀ j < n, t j = s j) := by
  let I (t : ℕ → Tree) := ∃ r a : List Bool,
    t n = encode Tree r ∧ t (n + 1) = encode Tree a ∧
      t (n + 4) = (encode Tree r).left ∧
      (encode Tree a).reverseAppend (encode Tree (BitList.increment r)) =
        encode Tree (BitList.increment bs) ∧
      (encode Tree r).size + (encode Tree a).size ≤ (encode Tree bs).size + 1 ∧
      a.length + r.length = bs.length ∧ ∀ j < n, t j = s j
  have hI : I s := ⟨bs, [], hr, ha, ht, by simp, by simp, by simp, fun _ _ ↦ rfl⟩
  have hloop := Bounded.whileNode (n := n + 5) (space := (encode Tree bs).size + 1)
    ⟨n + 4⟩ (succStep ⟨n⟩ ⟨n + 1⟩ ⟨n + 4⟩) I
    (fun t ↦ (t n).listLength) 13 hI
    (by
      intro t ⟨r, a, _, _, ht, _, hs, _, _⟩
      have := Tree.size_left_le (encode Tree r)
      simp only [Var.get_mk, ht]
      omega)
    (by
      intro t ⟨r, a, hr, ha, ht, hval, hs, hlen, hf⟩ hroot
      cases r with
      | nil => simp [Var.get, ht] at hroot
      | cons b r =>
        cases b with
        | false => simp [Var.get, ht] at hroot
        | true =>
          apply (succStep_bounded n t r a _ hr ha hs).mono (Nat.le_refl _) (Nat.le_refl _)
          intro _ u ⟨hur, hua, hut, huf⟩
          refine ⟨⟨r, false :: a, hur, hua, hut, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simpa [Tree.reverseAppend] using hval
          · simp at hs ⊢
            omega
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
          · exact fun j hj ↦ (huf j hj).trans (hf j hj)
          · simp only [hur, hr]
            simp)
  apply hloop.mono (by simp [hr]) (Nat.le_refl _)
  intro _ t ⟨⟨r, a, hr, ha, ht, hval, hs, hlen, hf⟩, hstop⟩
  refine ⟨r, a, hr, ha, ?_, hs, hlen, hf⟩
  have he : encode Tree (BitList.increment r) =
      Tree.pair (encode Tree true) (encode Tree r).right := by
    cases r with
    | nil => simp
    | cons b r => cases b <;> simp_all [Var.get]
  rwa [← he]

/-- A binary increment uses linear unit time in the number of digits and only constant
additional tree size. Earlier source values remain available for subsequent code. -/
theorem succ_bits_bounded (xs : Value) (n : ℕ) (s : ℕ → Tree) (bs : List Bool)
    (hx : xs.eval s = encode Tree bs) :
    (succ xs).Bounded n s (28 * bs.length + 25) ((encode Tree bs).size + 5)
      (fun v t ↦ v.eval t = encode Tree (BitList.increment bs) ∧ ∀ j < n, t j = s j) := by
  have hsteps := xs.assignSteps_le
  have hpos := Tree.size_pos (encode Tree bs)
  have hleft := Tree.size_left_le (encode Tree bs)
  unfold succ
  simp only [bounded_newVar_bind_iff, bounded_read_bind_iff, bounded_left_bind_iff]
  and_intros
  all_goals try (simp [hx] at * <;> omega)
  let u := Function.update (Function.update (Function.update (Function.update
    (Function.update s n (encode Tree bs)) (n + 1) .nil) (n + 2) (encode Tree bs))
      (n + 3) (encode Tree bs).left) (n + 4) (encode Tree bs).left
  apply Bounded.mono (time := (15 * bs.length + 2) + (13 * bs.length + 15)) ?_
    (by simp; omega) le_rfl (fun _ _ h ↦ h)
  have hloop := succLoop_bounded n u bs (by simp [u]) (by simp [u]) (by simp [u])
  apply Bounded.bind (by
    simpa (disch := omega) only [u, hx, Var.get_mk, Value.eval_nil, Value.eval_var,
      Function.update_self, Function.update_of_ne] using hloop.mono le_rfl
      (show (encode Tree bs).size + 1 ≤ (encode Tree bs).size + 5 by omega) (fun _ _ h ↦ h))
  intro _ t ⟨r, a, hr, ha, hval, hs, hlen, hf⟩
  have hright := Tree.size_right_le (encode Tree r)
  simp only [bounded_read_bind_iff, bounded_pair_bind_iff, bounded_right_bind_iff]
  and_intros
  all_goals try (simp [hr, ha] at * <;> omega)
  refine (List.Code.reverseAppend_bounded _ _ _ _ ?_).mono ?_ ?_ ?_
  · simp [Expr.bound]
  · simpa [ha] using (show a.length ≤ bs.length by omega)
  · simp [hr, ha] at *
    omega
  · intro v w ⟨hw, hframe⟩
    refine ⟨?_, ?_⟩
    · simpa [hr, ha, ← hval] using hw
    · intro j hj
      have hh := hframe j (by simp only [whileNode_build, succStep_build_snd_fst]; omega)
      simpa (disch := omega) [u, hf j hj] using hh

theorem succ_bounded (xs : Value) (n : ℕ) (s : ℕ → Tree) (a : ℕ)
    (hx : xs.eval s = encode Tree a) :
    (succ xs).Bounded n s (28 * a.bits.length + 25) ((encode Tree a).size + 5)
      (fun v t ↦ v.eval t = encode Tree (a + 1) ∧ ∀ j < n, t j = s j) := by
  simpa only [BitList.increment_bits, encode_nat_tree] using succ_bits_bounded xs n s a.bits hx

end Nat.Code
