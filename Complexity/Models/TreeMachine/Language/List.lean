/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Bounds
public import Complexity.Encoding.List

/-! # Iterative list programs

These ordinary `Code` definitions use the existing compact list encoding. Callbacks are
inlined while constructing the finite program; traversals do not need a runtime call stack.
-/

@[expose] public section

open Complexity TreeProgram TreeProgram.Code

namespace List.Code

/-- Move the next element from a cursor to a reversed accumulator. -/
@[simps! build_snd_fst]
def reverseStep (rest acc : Var) : TreeProgram.Code Unit := do
  let r ← read rest
  let a ← read acc
  write acc (← Value.pair (← r.left) a)
  write rest (← r.right)

/-- Reverse a list onto another list, sharing the unchanged element trees. -/
def reverseAppend (xs ys : Value) : TreeProgram.Code Value := do
  let rest ← newVar xs
  let acc ← newVar ys
  whileNode rest (reverseStep rest acc)
  read acc

/-- Reverse a list without traversing its elements. -/
def reverse (xs : Value) : TreeProgram.Code Value := reverseAppend xs .nil

/-- Append two lists by two linear traversals. -/
def append (xs ys : Value) : TreeProgram.Code Value := do
  reverseAppend (← reverse xs) ys

/-- Visit each encoded element. The callback may update captured source variables. -/
def forEach (xs : Value) (body : Value → TreeProgram.Code Unit) : TreeProgram.Code Unit := do
  let rest ← newVar xs
  whileNode rest do
    let r ← read rest
    body (← r.left)
    write rest (← r.right)

/-- Fold with a runtime accumulator. The callback returns one value and is inlined once. -/
def foldl (f : Value → Value → TreeProgram.Code Value) (init xs : Value) :
    TreeProgram.Code Value := do
  let acc ← newVar init
  forEach xs fun x ↦ do
    write acc (← f (← read acc) x)
  read acc

/-- Map an inlined element program, restoring the original order after accumulation. -/
def map (f : Value → TreeProgram.Code Value) (xs : Value) : TreeProgram.Code Value := do
  let acc ← foldl (fun acc x ↦ do Value.pair (← f x) acc) .nil xs
  reverse acc

private theorem reverseStep_bounded (rest acc : Var) (n : ℕ) (s : ℕ → Tree)
    (head tail a : Tree) (space : ℕ) (_hr : rest.index < n) (ha : acc.index < n)
    (hne : rest.index ≠ acc.index) (hsr : rest.get s = .pair head tail) (hsa : acc.get s = a)
    (hs : (Tree.pair head tail).size + a.size ≤ space) :
    (reverseStep rest acc).Bounded n s 11 space (fun _ t ↦
      rest.get t = tail ∧ acc.get t = .pair head a ∧
      ∀ j < n, j ≠ rest.index → j ≠ acc.index → t j = s j) := by
  simp only [Var.get] at hsr hsa
  simp +contextual (disch := omega) [reverseStep, Var.get, hsr, hsa, hne] at *
  omega

private theorem reverseLoop_bounded (n : ℕ) (s : ℕ → Tree) (space : ℕ)
    (hs : (s n).size + (s (n + 1)).size ≤ space) :
    (whileNode ⟨n⟩ (reverseStep ⟨n⟩ ⟨n + 1⟩)).Bounded (n + 2) s
      (13 * (s n).listLength + 2) space (fun _ t ↦
        t (n + 1) = (s n).reverseAppend (s (n + 1)) ∧ ∀ j < n, t j = s j) := by
  let I (t : ℕ → Tree) :=
    (t n).reverseAppend (t (n + 1)) = (s n).reverseAppend (s (n + 1)) ∧
      (t n).size + (t (n + 1)).size ≤ space ∧ ∀ j < n, t j = s j
  apply (Bounded.whileNode ⟨n⟩ (reverseStep ⟨n⟩ ⟨n + 1⟩) I
    (fun t ↦ (t n).listLength) 11 ⟨rfl, hs, fun _ _ ↦ rfl⟩ ?_ ?_).mono
      (Nat.le_refl _) (Nat.le_refl _)
  · intro _ t ⟨hI, hstop⟩
    have he : t n = .nil := Tree.root_eq_false.mp hstop
    exact ⟨by simpa only [he, Tree.reverseAppend] using hI.1, hI.2.2⟩
  · intro t ht
    have := ht.2.1
    change (t n).size ≤ space
    omega
  · intro t ht hroot
    cases hr : t n with
    | nil => simp [Var.get, hr] at hroot
    | node label head tail =>
      cases label
      apply (reverseStep_bounded ⟨n⟩ ⟨n + 1⟩ (n + 2) t head tail (t (n + 1)) space
        (by simp) (by simp) (by simp) hr rfl (by simpa only [hr] using ht.2.1)).mono
          (Nat.le_refl _) (Nat.le_refl _)
      intro _ u ⟨hur, hua, hf⟩
      change u n = tail at hur
      change u (n + 1) = .pair head (t (n + 1)) at hua
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simpa only [I, hur, hua, hr, Tree.reverseAppend] using ht.1
      · have := ht.2.1
        simp only [I, hur, hua, hr, Tree.size_pair] at *
        omega
      · intro j hj
        exact (hf j (by omega) (by change j ≠ n; omega)
          (by change j ≠ n + 1; omega)).trans (ht.2.2 j hj)
      · simp only [hur, Tree.listLength]
        omega

/-- A list reversal contract also preserves all earlier source values, so it composes with
other helpers. The one freshness condition prevents initializing the cursor over `ys`. -/
theorem reverseAppend_bounded (xs ys : Value) (n : ℕ) (s : ℕ → Tree)
    (hy : ys.expression.bound ≤ n) :
    (reverseAppend xs ys).Bounded n s
      (13 * (xs.eval s).listLength + 8) ((xs.eval s).size + (ys.eval s).size)
      (fun v t ↦ v.eval t = (xs.eval s).reverseAppend (ys.eval s) ∧
        ∀ j < n, t j = s j) := by
  have hy' := ys.eval_update_of_bound_le hy s (xs.eval s)
  have hxs := xs.assignSteps_le
  have hys := ys.assignSteps_le
  have hxpos := Tree.size_pos (xs.eval s)
  have hypos := Tree.size_pos (ys.eval s)
  simp only [reverseAppend, bounded_newVar_bind_iff, hy']
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  let u := Function.update (Function.update s n (xs.eval s)) (n + 1) (ys.eval s)
  have hu : (u n).size + (u (n + 1)).size ≤ (xs.eval s).size + (ys.eval s).size := by simp [u]
  have hloop := reverseLoop_bounded n u _ hu
  apply Bounded.mono (time := 13 * (xs.eval s).listLength + 2 + 2) ?_
    (by omega) (Nat.le_refl _) (fun _ _ h ↦ h)
  apply Bounded.bind (Q := fun _ t ↦
    t (n + 1) = (xs.eval s).reverseAppend (ys.eval s) ∧ ∀ j < n, t j = s j)
    (by simpa +contextual (disch := omega) [u, Nat.add_assoc] using hloop)
  intro v t ⟨ht, hf⟩
  have hout := Tree.size_reverseAppend (xs.eval s) (ys.eval s)
  simp only [bounded_read_iff, Var.get_mk]
  refine ⟨by decide, ?_, ?_⟩
  · rw [ht]
    omega
  constructor
  · simp [ht]
  · intro j hj
    simpa (disch := omega) [u] using hf j hj

theorem reverse_bounded (xs : Value) (n : ℕ) (s : ℕ → Tree) :
    (reverse xs).Bounded n s (13 * (xs.eval s).listLength + 8) ((xs.eval s).size + 1)
      (fun v t ↦ v.eval t = (xs.eval s).reverseAppend .nil ∧ ∀ j < n, t j = s j) :=
  reverseAppend_bounded xs .nil n s (Nat.zero_le _)

theorem append_bounded (xs ys : Value) (n : ℕ) (s : ℕ → Tree)
    (hy : ys.expression.bound ≤ n) :
    (append xs ys).Bounded n s (26 * (xs.eval s).listLength + 16)
      ((xs.eval s).size + (ys.eval s).size) (fun v t ↦
        v.eval t = ((xs.eval s).reverseAppend .nil).reverseAppend (ys.eval s) ∧
        ∀ j < n, t j = s j) := by
  have hypos := Tree.size_pos (ys.eval s)
  rw [show 26 * (xs.eval s).listLength + 16 =
    (13 * (xs.eval s).listLength + 8) + (13 * (xs.eval s).listLength + 8) by omega]
  apply Bounded.bind ((reverse_bounded xs n s).mono (Nat.le_refl _) (by omega)
    (fun _ _ h ↦ h))
  intro v t ⟨hv, hf⟩
  have hy' := ys.eval_eq_of_forall_lt hy hf
  have hs := Tree.size_reverseAppend (xs.eval s) .nil
  apply (reverseAppend_bounded v ys (n + 8) t (by omega)).mono
  · simp [hv]
  · simp only [hv, hy']
    simp only [Tree.size_nil] at hs
    omega
  · intro w u ⟨hw, hu⟩
    exact ⟨by simpa only [hv, hy'] using hw,
      fun j hj ↦ (hu j (by omega)).trans (hf j hj)⟩

end List.Code
