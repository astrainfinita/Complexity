/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Translation

/-! # Source specifications for Boolean and binary natural-number operations -/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

-- Binary operations reuse the source-loop compiler and the existing carry implementation.
@[source_bounds↓] def Implementation.bits : Implementation Nat.bits :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

@[scoped fun_prop] theorem bits_realizes : Realizes Nat.bits identityBounds :=
  Implementation.bits.realizes

def borrowContinues (x : List Bool × List Bool) : Bool :=
  match x.1 with | false :: _ => true | _ => false

def borrowStep (x : List Bool × List Bool) : List Bool × List Bool :=
  match x.1 with | _ :: xs => (xs, true :: x.2) | [] => x

def borrowFinish (x : List Bool × List Bool) : List Bool :=
  x.2.reverse ++ match x.1 with
    | true :: xs => if xs.isEmpty then [] else false :: xs
    | _ => []

def borrowContinuesImplementation : Implementation borrowContinues := by
  let h : Implementation borrowContinues := by source_cases
  refine h.rebudget ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩ ?_
  rintro ⟨xs, acc⟩
  cases xs with
  | nil => simp [h, source_bounds, borrowContinues]; omega
  | cons b bs => cases b <;> simp [h, source_bounds, borrowContinues] <;> omega

@[simp, source_bounds↓] theorem borrowContinuesImplementation_bounds :
    borrowContinuesImplementation.bounds = ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩ := rfl

def borrowStepImplementation : Implementation borrowStep := by
  let h : Implementation borrowStep := by source_cases
  refine h.rebudget ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size + 5⟩ ?_
  rintro ⟨xs, acc⟩
  cases xs <;> simp [h, source_bounds, borrowStep]
  omega

@[simp, source_bounds↓] theorem borrowStepImplementation_bounds :
    borrowStepImplementation.bounds = ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size + 5⟩ := rfl

def borrowFinishImplementation : Implementation borrowFinish := by
  let h : Implementation borrowFinish := by source_fun_prop
  refine h.rebudget
    ⟨fun x => 50 * x.2.length + 50, fun x => 2 * ⌜x⌝ₜ.size + 5⟩ ?_
  simp only [h, source_bounds]
  rintro ⟨xs, acc⟩
  cases xs with
  | nil => simp; omega
  | cons b bs => cases b <;> cases bs <;> simp <;> omega

@[simp, source_bounds↓] theorem borrowFinishImplementation_bounds :
    borrowFinishImplementation.bounds =
      ⟨fun x => 50 * x.2.length + 50, fun x => 2 * ⌜x⌝ₜ.size + 5⟩ := rfl

def borrow (x : List Bool × List Bool) := x.2.reverse ++ BitList.decrement x.1

def borrowImplementation : Implementation borrow := by
  refine .ofImplements
    (loopCode borrowContinuesImplementation.program borrowStepImplementation.program
      borrowFinishImplementation.program)
    ⟨fun x => 100 * ⌜x⌝ₜ.size + 100, fun x => 10 * ⌜x⌝ₜ.size + 10⟩ ?_
  let I (x y : List Bool × List Bool) :=
    y.1.length + y.2.length ≤ x.1.length + x.2.length ∧ borrow y = borrow x
  have sizeBound (x y) (h : I x y) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size := by
    rcases x with ⟨xs, acc⟩
    rcases y with ⟨ys, buf⟩
    have h₁ : ⌜ys⌝ₜ.size ≤ 4 * ys.length + 1 := Tree.size_encodeBitList_le _
    have h₂ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
    have hx₁ := length_le_codeSize xs
    have hx₂ := length_le_codeSize acc
    simp only [I, size_encode_prod] at *
    omega
  have hc := borrowContinuesImplementation.implements
  have hs := borrowStepImplementation.implements
  have hd := borrowFinishImplementation.implements
  rw [borrowContinuesImplementation_bounds] at hc
  rw [borrowStepImplementation_bounds] at hs
  rw [borrowFinishImplementation_bounds] at hd
  apply (Implements.loop hc hs hd
    (fun x => x.1.length) I (fun _ => 10) (fun x => 50 * ⌜x⌝ₜ.size + 50)
    (fun x => 10 * ⌜x⌝ₜ.size + 10) ?_ ?_ ?_ ?_ ?_).mono
  · rintro ⟨xs, acc⟩
    have := length_le_codeSize xs
    simp only [size_encode_prod]
    constructor <;> omega
  · intro x; exact ⟨le_rfl, rfl⟩
  · intro x y hi; have := sizeBound x y hi; omega
  · intro x y hi; have := sizeBound x y hi; exact ⟨le_rfl, by dsimp only; omega⟩
  · rintro x ⟨xs, acc⟩ hi ht
    have := sizeBound x (xs, acc) hi
    cases xs with
    | nil => simp [borrowContinues] at ht
    | cons b bs => cases b <;>
        simp_all [borrowContinues, borrowStep, I, borrow, List.reverse_cons,
          List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]; omega
  · rintro ⟨xs₀, acc₀⟩ ⟨xs, acc⟩ hi ht
    have := sizeBound (xs₀, acc₀) (xs, acc) hi
    have := length_le_codeSize xs₀
    have := length_le_codeSize acc₀
    refine ⟨?_, by dsimp only; omega, ?_⟩
    · have := hi.1
      simp only [size_encode_prod]
      dsimp only at *; omega
    · cases xs with
      | nil => simpa [borrowFinish, borrow] using hi.2
      | cons b bs => cases b <;> simp_all [borrowContinues, borrowFinish, I, borrow]

@[source_bounds↓] def Implementation.decrement :
    Implementation BitList.decrement := by
  let hb := borrowImplementation
  let h : Implementation (fun xs => borrow (xs, [])) := by source_fun_prop
  refine (Implementation.ofEncode (by intro xs; simp [borrow]) h).rebudget
    ⟨fun xs => 100 * ⌜xs⌝ₜ.size + 400, fun xs => 10 * ⌜xs⌝ₜ.size + 40⟩ ?_
  intro xs
  simp [h, hb, borrowImplementation, source_bounds]
  omega

@[scoped fun_prop] theorem decrement_realizes :
    Realizes BitList.decrement ⟨fun xs => 100 * ⌜xs⌝ₜ.size + 400,
      fun xs => 10 * ⌜xs⌝ₜ.size + 40⟩ := Implementation.decrement.realizes

def Implementation.pred : Implementation Nat.pred :=
  .ofEncode (by intro n; simp [Nat.pred_eq_sub_one])
    (Implementation.bits.comp Implementation.decrement)

@[simp, source_bounds↓] theorem Implementation.bounds_pred :
    Implementation.pred.bounds =
      ⟨fun n => 100 * ⌜n⌝ₜ.size + 400, fun n => 10 * ⌜n⌝ₜ.size + 40⟩ := by
  simp [Implementation.pred, source_bounds, compBounds]

@[scoped fun_prop] theorem pred_realizes :
    Realizes Nat.pred ⟨fun n => 100 * ⌜n⌝ₜ.size + 400, fun n => 10 * ⌜n⌝ₜ.size + 40⟩ := by
  simpa only [Implementation.bounds_pred] using Implementation.pred.realizes

@[source_bounds↓] def Implementation.boolNot : Implementation Bool.not := by
  let h : Implementation (fun x => match x with | false => true | true => false) := by source_cases
  refine (Implementation.ofEncode (by intro x; cases x <;> rfl) h).rebudget
    ⟨fun _ => 4, fun _ => 3⟩ ?_
  intro x
  cases x <;> simp [h, source_bounds]

@[scoped fun_prop] theorem bool_not_realizes :
    Realizes Bool.not ⟨fun _ => 4, fun _ => 3⟩ := Implementation.boolNot.realizes

@[source_bounds↓] def Implementation.boolAnd :
    Implementation (fun x : Bool × Bool => x.1 && x.2) := by
  let h : Implementation (fun x : Bool × Bool => match x.1 with | false => false | true => x.2) :=
    by source_cases
  refine (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl) h).rebudget
    ⟨fun _ => 6, fun x => ⌜x⌝ₜ.size + 2⟩ ?_
  rintro ⟨a, b⟩
  cases a <;> cases b <;> simp [h, source_bounds]

@[scoped fun_prop] theorem bool_and_realizes :
    Realizes (fun x : Bool × Bool => x.1 && x.2)
      ⟨fun _ => 6, fun x => ⌜x⌝ₜ.size + 2⟩ := Implementation.boolAnd.realizes

theorem bool_or_realizes :
    Realizes (fun x : Bool × Bool => x.1 || x.2)
      ⟨fun _ => 6, fun x => ⌜x⌝ₜ.size + 2⟩ := by
  apply Realizes.of_encode (g := fun x => match x.1 with | false => x.2 | true => true)
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl
  · source_cases

attribute [scoped fun_prop] bool_or_realizes

@[source_bounds↓] noncomputable def Implementation.boolOr :
    Implementation (fun x : Bool × Bool => x.1 || x.2) := bool_or_realizes.implementation

theorem bool_xor_realizes :
    Realizes (fun x : Bool × Bool => xor x.1 x.2)
      ⟨fun _ => 20, fun x => ⌜x⌝ₜ.size + 2⟩ := by
  apply Realizes.of_encode (g := fun x => match x.1 with | false => x.2 | true => !x.2)
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl
  · source_cases

attribute [scoped fun_prop] bool_xor_realizes

@[source_bounds↓] noncomputable def Implementation.boolXor :
    Implementation (fun x : Bool × Bool => xor x.1 x.2) := bool_xor_realizes.implementation

theorem bool_beq_realizes :
    Realizes (fun x : Bool × Bool => x.1 == x.2)
      ⟨fun _ => 24, fun x => ⌜x⌝ₜ.size + 2⟩ := by
  apply Realizes.of_encode (g := fun x => !(xor x.1 x.2))
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl
  · exact (bool_xor_realizes.comp bool_not_realizes).mono (by
      rintro ⟨a, b⟩
      simp only [compBounds]
      constructor
      · decide
      · have ha := Tree.size_pos ⌜a⌝ₜ
        have hb := Tree.size_pos ⌜b⌝ₜ
        simp only [size_encode_prod]
        omega)

attribute [scoped fun_prop] bool_beq_realizes

@[source_bounds↓] noncomputable def Implementation.boolBeq :
    Implementation (fun x : Bool × Bool => x.1 == x.2) := bool_beq_realizes.implementation

attribute [scoped fun_prop] Implementation.bits Implementation.decrement Implementation.pred
  Implementation.boolNot Implementation.boolAnd Implementation.boolOr Implementation.boolXor
  Implementation.boolBeq

private def addContinues (x : Bool × List Bool × List Bool × List Bool) : Bool :=
  !x.2.1.isEmpty && !x.2.2.1.isEmpty

private def addStep (x : Bool × List Bool × List Bool × List Bool) :=
  match x with
  | (c, a :: xs, b :: ys, acc) =>
      ((a && b) || (c && (a || b)), xs, ys, (xor (xor a b) c) :: acc)
  | _ => x

private def carryFinish (x : Bool × List Bool) :=
  if x.1 then BitList.increment x.2 else x.2

private theorem carryFinish_realizes :
    Realizes carryFinish ⟨fun x => 50 * ⌜x⌝ₜ.size + 50, fun x => ⌜x⌝ₜ.size + 5⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨c, xs⟩
  have := length_le_codeSize xs
  cases c <;> simp
  omega

private def addFinish (x : Bool × List Bool × List Bool × List Bool) :=
  let rest := if x.2.1.isEmpty then x.2.2.1 else x.2.1
  x.2.2.2.reverse ++ carryFinish (x.1, rest)

private def addResult (x : Bool × List Bool × List Bool × List Bool) :=
  x.2.2.2.reverse ++ BitList.addCarry x.1 x.2.1 x.2.2.1

private theorem addContinues_realizes :
    Realizes addContinues ⟨fun _ => 30, fun x => 2 * ⌜x⌝ₜ.size + 10⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨c, xs, ys, acc⟩
  cases c <;> cases xs <;> cases ys <;> simp <;> omega

private theorem addStep_realizes :
    Realizes addStep ⟨fun _ => 300, fun x => 2 * ⌜x⌝ₜ.size + 40⟩ := by
  refine Realizes.mono (by source_calls) ?_
  rintro ⟨c, xs, ys, acc⟩
  cases xs with
  | nil => simp [addStep]; omega
  | cons a xs =>
    cases ys with
    | nil => simp [addStep]; omega
    | cons b ys =>
      simp only [compBounds, pairBounds, projectionBounds, max_le_iff]
      cases c <;> cases a <;> cases b <;> simp <;> omega

private theorem addFinish_realizes :
    Realizes addFinish ⟨fun x => 100 * ⌜x⌝ₜ.size + 100, fun x => 2 * ⌜x⌝ₜ.size + 20⟩ := by
  have hc := carryFinish_realizes
  let implementation := hc.implementation
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨c, xs, ys, acc⟩
  have hx := length_le_codeSize xs
  have hy := length_le_codeSize ys
  have ha := length_le_codeSize acc
  have hsx : ⌜carryFinish (c, xs)⌝ₜ.size ≤ ⌜(c, xs)⌝ₜ.size + 5 := by
    simpa using hc.size_le (c, xs)
  have hsy : ⌜carryFinish (c, ys)⌝ₜ.size ≤ ⌜(c, ys)⌝ₜ.size + 5 := by
    simpa using hc.size_le (c, ys)
  simp only [compBounds, pairBounds, projectionBounds, appendBounds, reverseBounds, iteBounds]
  cases xs <;> simp only [List.isEmpty_nil, List.isEmpty_cons, ↓reduceIte,
    Bool.false_eq_true, size_encode_prod, encode_list_nil, size_encode_unit,
    size_encode_reverse, List.length_reverse, max_le_iff,
    encode_bool_true, encode_bool_false] at hsx hsy ⊢
  all_goals (repeat' apply And.intro) <;> omega

private theorem addResult_realizes :
    Realizes addResult ⟨fun x => 2000 * ⌜x⌝ₜ.size + 2000,
      fun x => 100 * ⌜x⌝ₜ.size + 100⟩ := by
  let count (x : Bool × List Bool × List Bool × List Bool) :=
    x.2.1.length + x.2.2.1.length + x.2.2.2.length
  let I x y := count y ≤ count x ∧ addResult y = addResult x
  have sizeBound x y (h : I x y) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
    rcases x with ⟨c, xs, ys, acc⟩
    rcases y with ⟨d, us, vs, buf⟩
    have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
    have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
    have h₃ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
    have hx := length_le_codeSize xs
    have hy := length_le_codeSize ys
    have ha := length_le_codeSize acc
    have hd := size_encode_bool_le d
    have hlen := h.1
    simp only [count] at hlen
    simp only [size_encode_prod]
    omega
  apply (Realizes.loop addContinues_realizes addStep_realizes addFinish_realizes
    (fun x => x.2.1.length) I (fun _ => 300)
    (fun x => 400 * ⌜x⌝ₜ.size + 1100) (fun x => 100 * ⌜x⌝ₜ.size + 100)
    ?_ ?_ ?_ ?_ ?_).mono
  · rintro ⟨c, xs, ys, acc⟩
    have := length_le_codeSize xs
    constructor <;> simp only [size_encode_prod] <;> omega
  · intro x; exact ⟨le_rfl, rfl⟩
  · intro x y hi; have := sizeBound x y hi; omega
  · intro x y hi; have := sizeBound x y hi; constructor <;> dsimp only <;> omega
  · rintro x ⟨c, xs, ys, acc⟩ hi ht
    have hsize := sizeBound x (c, xs, ys, acc) hi
    cases xs with
    | nil => simp [addContinues] at ht
    | cons a xs =>
      cases ys with
      | nil => simp [addContinues] at ht
      | cons b ys =>
        refine ⟨le_rfl, by dsimp only; omega, ⟨?_, ?_⟩, by simp [addStep]⟩
        · have := hi.1
          simp only [count, addStep, List.length_cons] at *
          omega
        · simpa only [addStep, addResult, BitList.addCarry, List.reverse_cons,
            List.append_assoc, List.singleton_append] using hi.2
  · rintro x ⟨c, xs, ys, acc⟩ hi ht
    have hsize := sizeBound x (c, xs, ys, acc) hi
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
    apply Eq.trans (b := addResult (c, xs, ys, acc)) ?_ hi.2
    cases xs <;> cases ys <;> simp [addContinues] at ht
    all_goals simp [addFinish, carryFinish, addResult, BitList.addCarry]

theorem add_realizes : Realizes (fun x : ℕ × ℕ => x.1 + x.2)
    ⟨fun x => 2000 * ⌜x⌝ₜ.size + 10020, fun x => 100 * ⌜x⌝ₜ.size + 1000⟩ := by
  let hadd := addResult_realizes.implementation
  apply Realizes.of_encode (g := fun x : ℕ × ℕ => addResult (false, x.1.bits, x.2.bits, []))
  · rintro ⟨m, n⟩; simp [addResult, BitList.addCarry_bits]
  · refine Realizes.mono (by source_fun_prop) ?_
    rintro ⟨m, n⟩
    simp
    omega

attribute [scoped fun_prop] add_realizes

@[source_bounds↓] noncomputable def Implementation.add :
    Implementation (fun x : ℕ × ℕ => x.1 + x.2) := add_realizes.implementation

private def leContinues (x : Bool × List Bool × List Bool) :=
  !(x.2.1.isEmpty && x.2.2.isEmpty)

private def leStep (x : Bool × List Bool × List Bool) :=
  match x with
  | (c, [], b :: ys) => (b || c, [], ys)
  | (c, a :: xs, []) => (!a && c, xs, [])
  | (c, a :: xs, b :: ys) => ((if a == b then c else b), xs, ys)
  | _ => x

private def leResult (x : Bool × List Bool × List Bool) := BitList.leAux x.1 x.2.1 x.2.2

private theorem leContinues_realizes :
    Realizes leContinues ⟨fun _ => 30, fun x => 2 * ⌜x⌝ₜ.size + 10⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨c, xs, ys⟩
  cases c <;> cases xs <;> cases ys <;> simp <;> omega

private theorem leStep_realizes :
    Realizes leStep ⟨fun _ => 100, fun x => 2 * ⌜x⌝ₜ.size + 20⟩ := by
  refine Realizes.mono (by source_calls) ?_
  rintro ⟨c, xs, ys⟩
  cases xs with
  | nil => cases ys <;> cases c <;> dsimp only [leStep] <;> simp <;> omega
  | cons a xs =>
    cases ys with
    | nil => cases c <;> cases a <;> simp <;> omega
    | cons b ys =>
      simp only [compBounds, pairBounds, projectionBounds, iteBounds, max_le_iff]
      cases c <;> cases a <;> cases b <;> simp <;> omega

private theorem leResult_realizes :
    Realizes leResult ⟨fun x => 1000 * ⌜x⌝ₜ.size + 100,
      fun x => 100 * ⌜x⌝ₜ.size + 100⟩ := by
  let count (x : Bool × List Bool × List Bool) := x.2.1.length + x.2.2.length
  let I x y := count y ≤ count x ∧ leResult y = leResult x
  have sizeBound x y (h : I x y) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
    rcases x with ⟨c, xs, ys⟩
    rcases y with ⟨d, us, vs⟩
    have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
    have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
    have hx := length_le_codeSize xs
    have hy := length_le_codeSize ys
    have hd := size_encode_bool_le d
    have hlen := h.1
    simp only [count] at hlen
    simp only [size_encode_prod]
    omega
  apply (Realizes.loop leContinues_realizes leStep_realizes fst_realizes
    count I (fun _ => 100) (fun _ => 1) (fun x => 100 * ⌜x⌝ₜ.size + 100)
    ?_ ?_ ?_ ?_ ?_).mono
  · rintro ⟨c, xs, ys⟩
    have := length_le_codeSize xs
    have := length_le_codeSize ys
    constructor <;> simp only [count, size_encode_prod] <;> omega
  · intro x; exact ⟨le_rfl, rfl⟩
  · intro x y hi; have := sizeBound x y hi; omega
  · intro x y hi; have := sizeBound x y hi; constructor <;> dsimp only <;> omega
  · rintro x ⟨c, xs, ys⟩ hi ht
    have := sizeBound x (c, xs, ys) hi
    refine ⟨le_rfl, by dsimp only; omega, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have := hi.1
        cases xs <;> cases ys <;> simp_all only [leStep, count, List.length_nil, List.length_cons]
        all_goals omega
      · cases xs <;> cases ys <;> simpa only [leStep, leResult, BitList.leAux] using hi.2
    · cases xs <;> cases ys <;> simp [leContinues] at ht
      all_goals simp [leStep, count] <;> omega
  · rintro x ⟨c, xs, ys⟩ hi ht
    have := sizeBound x (c, xs, ys) hi
    refine ⟨le_rfl, by dsimp only [projectionBounds]; omega, ?_⟩
    have hnil : xs = [] ∧ ys = [] := by simpa [leContinues] using ht
    rcases hnil with ⟨rfl, rfl⟩
    simpa [leResult, BitList.leAux] using hi.2

private theorem compare_realizes (c : Bool) :
    Realizes (fun x : ℕ × ℕ => leResult (c, x.1.bits, x.2.bits))
      ⟨fun x => 1000 * ⌜x⌝ₜ.size + 10000, fun x => 100 * ⌜x⌝ₜ.size + 1000⟩ := by
  let hle := leResult_realizes.implementation
  cases c <;> refine Realizes.mono (by source_fun_prop) ?_
  all_goals rintro ⟨m, n⟩; simp; omega

theorem ble_realizes : Realizes (fun x : ℕ × ℕ => Nat.ble x.1 x.2)
    ⟨fun x => 1000 * ⌜x⌝ₜ.size + 10000, fun x => 100 * ⌜x⌝ₜ.size + 1000⟩ := by
  apply Realizes.of_encode (hg := compare_realizes true)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

theorem lt_realizes : Realizes (fun x : ℕ × ℕ => decide (x.1 < x.2))
    ⟨fun x => 1000 * ⌜x⌝ₜ.size + 10000, fun x => 100 * ⌜x⌝ₜ.size + 1000⟩ := by
  apply Realizes.of_encode (hg := compare_realizes false)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

attribute [scoped fun_prop] ble_realizes

@[source_bounds↓] noncomputable def Implementation.ble :
    Implementation (fun x : ℕ × ℕ => Nat.ble x.1 x.2) := ble_realizes.implementation

attribute [scoped fun_prop] Implementation.add Implementation.ble

-- Recognize source strict comparisons before their successor/ble implementation is expanded.
open Lean Meta Mathlib.Meta.FunProp in
run_elab addTheorem ``lt_realizes .scoped 2000

@[source_bounds↓] noncomputable def Implementation.lt :
    Implementation (fun x : ℕ × ℕ => decide (x.1 < x.2)) := lt_realizes.implementation

open Lean Meta Mathlib.Meta.FunProp in
run_elab addTheorem ``Implementation.lt .scoped 2000

/-- Equality uses the same binary comparison implementation in both directions. -/
theorem nat_beq_realizes : Realizes (fun x : ℕ × ℕ => Nat.beq x.1 x.2)
    ⟨fun x => 3000 * ⌜x⌝ₜ.size + 30000, fun x => 100 * ⌜x⌝ₜ.size + 2000⟩ := by
  apply Realizes.of_encode (g := fun x : ℕ × ℕ => Nat.ble x.1 x.2 && Nat.ble x.2 x.1)
  · rintro ⟨m, n⟩
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp [Nat.le_antisymm_iff]
  · refine Realizes.mono (by source_fun_prop) ?_
    rintro ⟨m, n⟩
    have hm := size_encode_bool_le (Nat.ble m n)
    have hn := size_encode_bool_le (Nat.ble n m)
    simp only [compBounds, pairBounds, projectionBounds, size_encode_prod, max_le_iff]
    (repeat' apply And.intro) <;> omega

attribute [scoped fun_prop] nat_beq_realizes

@[source_bounds↓] noncomputable def Implementation.natBeq :
    Implementation (fun x : ℕ × ℕ => Nat.beq x.1 x.2) := nat_beq_realizes.implementation

attribute [scoped fun_prop] Implementation.natBeq

end Complexity.TreeProgram.Source
