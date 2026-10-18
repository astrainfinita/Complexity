/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for Boolean and binary natural-number operations -/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

-- Binary operations reuse the source-loop compiler and the existing carry implementation.
def Implementation.bits : Implementation Nat.bits (fun _ => 0) (fun _ => 0) :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

def borrowContinues (x : List Bool × List Bool) : Bool :=
  match x.1 with | false :: _ => true | _ => false

def borrowStep (x : List Bool × List Bool) : List Bool × List Bool :=
  match x.1 with | _ :: xs => (xs, true :: x.2) | [] => x

def borrowFinish (x : List Bool × List Bool) : List Bool :=
  x.2.reverse ++ match x.1 with
    | true :: xs => if xs.isEmpty then [] else false :: xs
    | _ => []

def borrowContinuesImplementation :
    Implementation borrowContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_cases
  all_goals dominated

def borrowStepImplementation :
    Implementation borrowStep (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_cases
  all_goals dominated [borrowStep]

def borrow (x : List Bool × List Bool) := x.2.reverse ++ BitList.decrement x.1

def borrowFinishImplementation :
    Implementation borrowFinish (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated


attribute [scoped fun_prop] borrowContinuesImplementation borrowStepImplementation
  borrowFinishImplementation

def borrowInvariant (x y : List Bool × List Bool) : Prop :=
  y.1.length + y.2.length ≤ x.1.length + x.2.length

theorem borrowInvariant_size : Dominated
    (fun z : {p : (List Bool × List Bool) × (List Bool × List Bool) //
      borrowInvariant p.1 p.2} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  apply Dominated.of_le_mul 4
  rintro ⟨⟨⟨xs, acc⟩, ⟨ys, buf⟩⟩, h⟩
  have h₁ : ⌜ys⌝ₜ.size ≤ 4 * ys.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
  have hx₁ := length_le_codeSize xs
  have hx₂ := length_le_codeSize acc
  simp only [size_encode_prod] at *
  change ys.length + buf.length ≤ xs.length + acc.length at h
  omega

/-- The loop consumes callback growth specifications; no overall credit constant is supplied. -/
def borrowImplementation : Implementation borrow (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop using loop (test := borrowContinues) (next := borrowStep)
    (finish := borrowFinish) (invariant := borrowInvariant) (measure := fun x => x.1.length)
    (step := fun _ => 1) (stop := fun x => ⌜x⌝ₜ.size) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨xs, acc⟩
    cases xs with
    | nil => simp [borrow, borrowContinues, borrowFinish, BitList.decrement]
    | cons b bs => cases b <;> simp [borrow, borrowContinues, borrowStep, borrowFinish,
        BitList.decrement, List.reverse_cons, List.append_assoc]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro ⟨xs, acc⟩ ⟨ys, buf⟩ hi ht
    cases ys <;> simp_all [borrowContinues, borrowStep, borrowInvariant]
    omega
  case decreases =>
    rintro x ⟨ys, buf⟩ _ ht
    cases ys <;> simp_all [borrowContinues, borrowStep]
  case input_size => exact borrowInvariant_size
  case check_peak => exact borrowInvariant_size
  case step_peak => exact borrowInvariant_size
  case stop_peak => exact borrowInvariant_size
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact borrowInvariant_size
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _
  case time =>
    simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated (fun x : List Bool × List Bool => x.1.length)
        (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x =>
      (length_le_codeSize x.1).trans (size_encode_fst_le x)
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.refl _⟩⟩, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩

def Implementation.decrement :
    Implementation BitList.decrement (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  let hb := borrowImplementation
  source_fun_prop via (fun xs => borrow (xs, []))
  case source_eq => funext xs; simp [borrow]
  all_goals dominated

def Implementation.pred : Implementation Nat.pred (fun n => ⌜n⌝ₜ.size) (fun n => ⌜n⌝ₜ.size) :=
  (Implementation.ofEncode (by intro n; simp [Nat.pred_eq_sub_one])
    (Implementation.bits.comp Implementation.decrement)).mono
    (Dominated.of_le fun n => by simp)
    (Dominated.of_le fun n => by simp)

/-- A Boolean result has a constant-size code. -/
theorem dominated_size_encode_bool {α : Type*} [UniqueEncoding Tree α] (f : α → Bool) :
    Dominated (fun x => max ⌜x⌝ₜ.size ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
  (Dominated.refl _).max_same ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
    fun _ => size_encode_bool_le _)

def Implementation.boolNot : Implementation Bool.not (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by intro x; cases x <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x => match x with | false => true | true => false)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolAnd :
    Implementation (fun x : Bool × Bool => x.1 && x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => false | true => x.2)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolOr :
    Implementation (fun x : Bool × Bool => x.1 || x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => true)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolXor :
    Implementation (fun x : Bool × Bool => xor x.1 x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => !x.2)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolBeq :
    Implementation (fun x : Bool × Bool => x.1 == x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (Implementation.boolXor.comp Implementation.boolNot)).mono (Dominated.const 2)
    (dominated_size_encode_bool _)

attribute [scoped fun_prop] Implementation.bits Implementation.decrement Implementation.pred
  Implementation.boolNot Implementation.boolAnd Implementation.boolOr Implementation.boolXor
  Implementation.boolBeq

def addContinues (x : Bool × List Bool × List Bool × List Bool) : Bool :=
  !x.2.1.isEmpty && !x.2.2.1.isEmpty

def addStep (x : Bool × List Bool × List Bool × List Bool) :=
  match x with
  | (c, a :: xs, b :: ys, acc) =>
      ((a && b) || (c && (a || b)), xs, ys, (xor (xor a b) c) :: acc)
  | _ => x

def carryFinish (x : Bool × List Bool) :=
  if x.1 then BitList.increment x.2 else x.2

def carryFinishImplementation :
    Implementation carryFinish (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated


attribute [local fun_prop] carryFinishImplementation


def addFinish (x : Bool × List Bool × List Bool × List Bool) :=
  let rest := if x.2.1.isEmpty then x.2.2.1 else x.2.1
  x.2.2.2.reverse ++ carryFinish (x.1, rest)

def addResult (x : Bool × List Bool × List Bool × List Bool) :=
  x.2.2.2.reverse ++ BitList.addCarry x.1 x.2.1 x.2.2.1

def addContinuesImplementation :
    Implementation addContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hb (f : Bool × List Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  source_fun_prop
  all_goals dominated


attribute [local fun_prop] addContinuesImplementation


def addStepImplementation : Implementation addStep (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_calls
  all_goals dominated [addStep]


attribute [local fun_prop] addStepImplementation


def addFinishImplementation :
    Implementation addFinish (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have hcarryInput : Dominated
      (fun x : Bool × List Bool × List Bool × List Bool =>
        ⌜(x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1)⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨c, xs, ys, acc⟩
    simp only [size_encode_prod]
    split <;> omega
  have hcarry := (carryFinishImplementation.size_encode.comp
    (fun x : Bool × List Bool × List Bool × List Bool =>
      (x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1))).trans
      (hcarryInput.max_same hcarryInput)
  source_fun_prop
  all_goals dominated


attribute [local fun_prop] addFinishImplementation


def addCount (x : Bool × List Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.1.length + x.2.2.2.length

theorem addCount_size (x y : Bool × List Bool × List Bool × List Bool)
    (h : addCount y ≤ addCount x) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
  rcases x with ⟨c, xs, ys, acc⟩
  rcases y with ⟨d, us, vs, buf⟩
  have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
  have h₃ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
  have hx := length_le_codeSize xs
  have hy := length_le_codeSize ys
  have ha := length_le_codeSize acc
  have hd := size_encode_bool_le d
  simp only [addCount, size_encode_prod] at *
  omega

theorem addCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool × List Bool) ×
      (Bool × List Bool × List Bool × List Bool) // addCount p.2 ≤ addCount p.1} => ⌜z.1.2⌝ₜ.size)
    (fun z => ⌜z.1.1⌝ₜ.size) :=
  (((Dominated.refl _).const_mul_left 4).add_same
    (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)).mono_left
      fun z => addCount_size _ _ z.2

def addResultImplementation :
    Implementation addResult (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop using loop (test := addContinues) (next := addStep) (finish := addFinish)
    (invariant := fun x y => addCount y ≤ addCount x) (measure := fun x => x.2.1.length)
    (step := fun _ => 1) (stop := fun x => ⌜x⌝ₜ.size) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨c, xs, ys, acc⟩
    cases xs <;> cases ys <;> simp [addResult, addContinues, addStep, addFinish,
      carryFinish, BitList.addCarry, List.reverse_cons, List.append_assoc]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro x ⟨c, xs, ys, acc⟩ hi ht
    cases xs <;> cases ys <;> simp_all [addContinues, addStep, addCount]
    omega
  case decreases =>
    rintro x ⟨c, xs, ys, acc⟩ _ ht
    cases xs <;> cases ys <;> simp_all [addContinues, addStep]
  case input_size => exact addCount_size_growth
  case check_peak => exact addCount_size_growth
  case step_peak => exact addCount_size_growth
  case stop_peak => exact addCount_size_growth
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact addCount_size_growth
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _
  case time =>
    simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated (fun x : Bool × List Bool × List Bool × List Bool => x.2.1.length)
        (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x =>
      (length_le_codeSize x.2.1).trans ((size_encode_fst_le x.2).trans (size_encode_snd_le x))
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.refl _⟩⟩, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩

def Implementation.add :
    Implementation (fun x : ℕ × ℕ => x.1 + x.2) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  let hadd := addResultImplementation
  refine Implementation.ofEncode
    (g := fun x : ℕ × ℕ => addResult (false, x.1.bits, x.2.bits, [])) ?_ ?_
  · rintro ⟨m, n⟩; simp [addResult, BitList.addCarry_bits]
  source_fun_prop
  all_goals dominated

def leContinues (x : Bool × List Bool × List Bool) :=
  !(x.2.1.isEmpty && x.2.2.isEmpty)

def leStep (x : Bool × List Bool × List Bool) :=
  match x with
  | (c, [], b :: ys) => (b || c, [], ys)
  | (c, a :: xs, []) => (!a && c, xs, [])
  | (c, a :: xs, b :: ys) => ((if a == b then c else b), xs, ys)
  | _ => x

def leResult (x : Bool × List Bool × List Bool) := BitList.leAux x.1 x.2.1 x.2.2

def leContinuesImplementation :
    Implementation leContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hb (f : Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  source_fun_prop
  all_goals dominated


attribute [local fun_prop] leContinuesImplementation


def leStepImplementation : Implementation leStep (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_calls
  all_goals dominated [leStep]


attribute [local fun_prop] leStepImplementation


def compareCount (x : Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.length

theorem compareCount_size (x y : Bool × List Bool × List Bool)
    (h : compareCount y ≤ compareCount x) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
  rcases x with ⟨c, xs, ys⟩
  rcases y with ⟨d, us, vs⟩
  have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
  have hx := length_le_codeSize xs
  have hy := length_le_codeSize ys
  have hd := size_encode_bool_le d
  simp only [compareCount, size_encode_prod] at *
  omega

theorem compareCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool) × (Bool × List Bool × List Bool) //
      compareCount p.2 ≤ compareCount p.1} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) :=
  (((Dominated.refl _).const_mul_left 4).add_same
    (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)).mono_left
      fun z => compareCount_size _ _ z.2

def leResultImplementation :
    Implementation leResult (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop using loop (test := leContinues) (next := leStep) (finish := Prod.fst)
    (invariant := fun x y => compareCount y ≤ compareCount x) (measure := compareCount)
    (step := fun _ => 1) (stop := fun _ => 1) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨c, xs, ys⟩
    cases xs <;> cases ys <;> simp [leContinues, leStep, leResult, BitList.leAux]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro x ⟨c, xs, ys⟩ hi ht
    cases xs <;> cases ys <;> simp_all [leContinues, leStep, compareCount]
    all_goals omega
  case decreases =>
    rintro x ⟨c, xs, ys⟩ _ ht
    cases xs <;> cases ys <;> simp_all [leContinues, leStep, compareCount]
    all_goals omega
  case input_size => exact compareCount_size_growth
  case check_peak => exact compareCount_size_growth
  case step_peak => exact compareCount_size_growth
  case stop_peak => exact compareCount_size_growth
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time =>
    simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated compareCount (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x => by
      rcases x with ⟨c, xs, ys⟩
      have := length_le_codeSize xs
      have := length_le_codeSize ys
      dsimp only [compareCount]
      simp only [size_encode_prod]
      omega
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩⟩,
      Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩

def compareImplementation (c : Bool) :
    Implementation (fun x : ℕ × ℕ => leResult (c, x.1.bits, x.2.bits))
      (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  let hle := leResultImplementation
  cases c <;> source_fun_prop
  all_goals dominated

def Implementation.ble :
    Implementation (fun x : ℕ × ℕ => Nat.ble x.1 x.2) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  apply Implementation.ofEncode (hg := compareImplementation true)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

def Implementation.lt :
    Implementation (fun x : ℕ × ℕ => decide (x.1 < x.2)) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  apply Implementation.ofEncode (hg := compareImplementation false)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

attribute [scoped fun_prop] Implementation.add Implementation.ble Implementation.lt

def Implementation.natBeq :
    Implementation (fun x : ℕ × ℕ => Nat.beq x.1 x.2) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop via (fun x : ℕ × ℕ => Nat.ble x.1 x.2 && Nat.ble x.2 x.1)
  case source_eq =>
    funext ⟨m, n⟩
    apply Bool.eq_iff_iff.mpr
    simp [Nat.le_antisymm_iff]
  all_goals
    simp only [size_encode_prod, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
      | exact Dominated.of_le size_encode_fst_le
      | exact Dominated.of_le size_encode_snd_le
      | exact (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
          fun x => size_encode_bool_le _

attribute [scoped fun_prop] Implementation.natBeq

end Complexity.TreeProgram.Source
