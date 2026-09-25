/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree
public import Mathlib.Data.Int.Basic

/-!
# Prefix codes for binary trees

The code uses one bit for each node: `false` for a leaf and `true` for a pair.
It is intended for internal machine simulations. Parsing consumes exactly one
tree, leaving an arbitrary suffix untouched.
-/

@[expose] public section

namespace Complexity.BitList

open Complexity.Tree

/-- The prefix code of a tree, with one bit per node. -/
def encodeTree : Tree → List Bool
  | nil => [false]
  | pair a b => true :: (encodeTree a ++ encodeTree b)

@[simp] theorem encodeTree_nil : encodeTree nil = [false] := rfl

@[simp] theorem encodeTree_pair (a b : Tree) :
    encodeTree (pair a b) = true :: (encodeTree a ++ encodeTree b) := rfl

@[simp] theorem length_encodeTree (a : Tree) : (encodeTree a).length = size a := by
  induction a with
  | nil => rfl
  | node v a b ha hb =>
      cases v
      simp [ha, hb, Nat.add_comm, Nat.add_assoc]

/-- Parse one prefix-coded tree with a bound on the recursion depth. -/
def parseTreeFuel : ℕ → List Bool → Option (Tree × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: xs => some (nil, xs)
  | n + 1, true :: xs => do
      let (a, ys) ← parseTreeFuel n xs
      let (b, zs) ← parseTreeFuel n ys
      pure (pair a b, zs)

/-- Parse the first tree, returning the unconsumed suffix. -/
def parseTree (xs : List Bool) : Option (Tree × List Bool) :=
  parseTreeFuel xs.length xs

theorem parseTreeFuel_encodeTree_append (a : Tree) (xs : List Bool) {n : ℕ}
    (h : size a ≤ n) : parseTreeFuel n (encodeTree a ++ xs) = some (a, xs) := by
  induction a generalizing n xs with
  | nil =>
      cases n with
      | zero => simp at h
      | succ n => rfl
  | node v a b ha hb =>
      cases v
      cases n with
      | zero => simp [size] at h
      | succ n =>
          have ha' : size a ≤ n := by simp only [size_pair] at h; omega
          have hb' : size b ≤ n := by simp only [size_pair] at h; omega
          simp [List.append_assoc, parseTreeFuel, ha _ ha', hb _ hb']

@[simp] theorem parseTree_encodeTree_append (a : Tree) (xs : List Bool) :
    parseTree (encodeTree a ++ xs) = some (a, xs) := by
  apply parseTreeFuel_encodeTree_append
  simp

@[simp] theorem parseTree_encodeTree (a : Tree) : parseTree (encodeTree a) = some (a, []) := by
  simpa using parseTree_encodeTree_append a []

theorem parseTreeFuel_sound {n : ℕ} {xs ys : List Bool} {a : Tree}
    (h : parseTreeFuel n xs = some (a, ys)) : xs = encodeTree a ++ ys := by
  induction n generalizing xs ys a with
  | zero => simp [parseTreeFuel] at h
  | succ n ih =>
      cases xs with
      | nil => simp [parseTreeFuel] at h
      | cons b xs =>
          cases b with
          | false =>
              simp only [parseTreeFuel, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
          | true =>
              cases ha : parseTreeFuel n xs with
              | none => simp [parseTreeFuel, ha] at h
              | some p =>
                  obtain ⟨a, zs⟩ := p
                  cases hb : parseTreeFuel n zs with
                  | none => simp [parseTreeFuel, ha, hb] at h
                  | some p =>
                      obtain ⟨b, ws⟩ := p
                      simp only [parseTreeFuel, ha, Option.pure_def, Option.bind_eq_bind,
                        Option.bind_some, hb, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      simp [ih ha, ih hb, List.append_assoc]

/-- Successful parsing is equivalent to splitting off the exact tree code. -/
theorem parseTree_eq_some_iff {xs ys : List Bool} {a : Tree} :
    parseTree xs = some (a, ys) ↔ xs = encodeTree a ++ ys := by
  constructor
  · exact parseTreeFuel_sound
  · rintro rfl
    exact parseTree_encodeTree_append a ys

theorem encodeTree_injective : Function.Injective encodeTree := by
  intro a b h
  have := congrArg parseTree h
  simpa using this

@[simp] theorem encodeTree_inj {a b : Tree} : encodeTree a = encodeTree b ↔ a = b :=
  encodeTree_injective.eq_iff

/-- Complete tree codes have unique boundaries, even with arbitrary suffixes. -/
theorem encodeTree_append_eq_iff {a b : Tree} {xs ys : List Bool} :
    encodeTree a ++ xs = encodeTree b ++ ys ↔ a = b ∧ xs = ys := by
  constructor
  · intro h
    have := congrArg parseTree h
    simpa using this
  · rintro ⟨rfl, rfl⟩
    rfl

/-- No complete tree code is a proper prefix of another. -/
@[simp] theorem encodeTree_prefix_iff {a b : Tree} : encodeTree a <+: encodeTree b ↔ a = b := by
  constructor
  · rintro ⟨xs, h⟩
    exact (encodeTree_append_eq_iff (xs := xs) (ys := []).mp (by simpa using h)).1
  · rintro rfl
    exact List.prefix_rfl

/-- Skip a forest described by its number of pending subtrees. -/
def scan : ℕ → List Bool → Option (List Bool)
  | 0, xs => some xs
  | _ + 1, [] => none
  | n + 1, false :: xs => scan n xs
  | n + 1, true :: xs => scan (n + 2) xs

/-- Scanning a tree consumes one pending subtree and exactly its code. -/
theorem scan_encodeTree_append (a : Tree) (n : ℕ) (xs : List Bool) :
    scan (n + 1) (encodeTree a ++ xs) = scan n xs := by
  induction a generalizing n xs with
  | nil => rfl
  | node v a b ha hb =>
      cases v
      simp only [encodeTree_pair, List.cons_append, List.append_assoc, scan]
      rw [ha, hb]

@[simp] theorem scan_one_encodeTree_append (a : Tree) (xs : List Bool) :
    scan 1 (encodeTree a ++ xs) = some xs := by
  simpa only [scan] using scan_encodeTree_append a 0 xs

/-- The change in the number of pending subtrees along a bit string. -/
def balance : List Bool → ℤ
  | [] => 0
  | b :: xs => (if b then 1 else -1) + balance xs

@[simp] theorem balance_nil : balance [] = 0 := rfl

@[simp] theorem balance_cons_true (xs : List Bool) :
    balance (true :: xs) = 1 + balance xs := rfl

@[simp] theorem balance_cons_false (xs : List Bool) :
    balance (false :: xs) = -1 + balance xs := rfl

@[simp] theorem balance_append (xs ys : List Bool) :
    balance (xs ++ ys) = balance xs + balance ys := by
  induction xs with
  | nil => simp
  | cons b xs h => simp [balance, h, Int.add_assoc]

@[simp] theorem balance_encodeTree (a : Tree) : balance (encodeTree a) = -1 := by
  induction a with
  | nil => rfl
  | node v a b ha hb => cases v; simp [ha, hb]

/-- A proper prefix leaves at least one subtree pending. -/
theorem balance_take_encodeTree_nonneg (a : Tree) {n : ℕ} (h : n < size a) :
    0 ≤ balance ((encodeTree a).take n) := by
  induction a generalizing n with
  | nil =>
      have : n = 0 := by simpa using h
      simp [this]
  | node v a b ha hb =>
      cases v
      cases n with
      | zero => simp
      | succ n =>
          simp only [encodeTree_pair, List.take_succ_cons, balance_cons_true]
          by_cases hn : n < size a
          · rw [List.take_append_of_le_length (by simpa using Nat.le_of_lt hn)]
            have := ha hn
            omega
          · have hn' : n = (encodeTree a).length + (n - size a) := by
              rw [length_encodeTree]
              omega
            rw [hn', List.take_length_add_append, balance_append, balance_encodeTree]
            have : n - size a < size b := by simp only [size_pair] at h; omega
            have := hb this
            omega

/-- The first zero of the pending-subtree counter is the exact end of the code. -/
theorem balance_take_encodeTree_eq_neg_one_iff (a : Tree) {n : ℕ} (h : n ≤ size a) :
    balance ((encodeTree a).take n) = -1 ↔ n = size a := by
  constructor
  · intro hn
    by_contra he
    have := balance_take_encodeTree_nonneg a (by omega : n < size a)
    omega
  · rintro rfl
    simpa only [← length_encodeTree, List.take_length] using balance_encodeTree a

end Complexity.BitList
