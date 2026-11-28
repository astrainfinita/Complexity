/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Iteration
public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for binary arithmetic and finite vectors -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

theorem _root_.List.hasProgramIn_tail {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.tail : List α → List α) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programTail
  fill_hole program in source_fun_prop

attribute [program] List.hasProgramIn_tail

/-- Whether the indexed lookup continues: the list is nonempty and the index, read through its
binary digits, is nonzero. -/
def lookupContinues {α : Type*} (x : ℕ × List α) : Bool :=
  match x.2 with | [] => false | _ :: _ => !x.1.bits.isEmpty

/-- Decrease the index by one and drop the head of the list. -/
def lookupStep {α : Type*} (x : ℕ × List α) := (x.1.pred, x.2.tail)

theorem hasProgramIn_lookupContinues {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (lookupContinues (α := α)) hole(⊢ program) IsO(fun _ => 1)
      IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupContinues
  fill_hole program in source_fun_prop

theorem hasProgramIn_lookupStep {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (lookupStep (α := α)) hole(⊢ program)
      IsO(fun x => ⌜x.1⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupStep
  have := Nat.hasProgramIn_pred.toHasProgramInO.size_encode.comp (fun x : ℕ × List α => x.1)
  fill_hole program in source_fun_prop

theorem hasProgramIn_lookupFinish {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (fun x : ℕ × List α => x.2.head?) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupFinish
  fill_hole program in source_fun_prop

/-- The invariant of the indexed lookup: a reached state has an index with no more binary digits, a
list code no larger than the input's, and the same looked-up entry. -/
def lookupInvariant {α : Type*} [UniqueEncoding Tree α] (x y : ℕ × List α) :=
  y.1.bits.length ≤ x.1.bits.length ∧ ⌜y.2⌝ₜ.size ≤ ⌜x.2⌝ₜ.size ∧ y.2[y.1]? = x.2[x.1]?

theorem lookup_size {α : Type*} [UniqueEncoding Tree α] :
    Dominated (fun z : {p : (ℕ × List α) × (ℕ × List α) // lookupInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [lookupInvariant, size_encode_nat_le_length_bits]

/-- Indexed lookup uses selected callbacks and one invariant-family growth specification. -/
theorem hasProgramIn_lookup {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (fun x : ℕ × List α => x.2[x.1]?) hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size ^ 2)
      IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookup
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    refine (HasProgramInO.tail_loop hasProgramIn_lookupContinues.toHasProgramInO
      hasProgramIn_lookupStep.toHasProgramInO
      hasProgramIn_lookupFinish.toHasProgramInO lookupInvariant
      (fun x => x.2.length) (fun x => ⌜x⌝ₜ.size) (fun _ => 1) (fun x => ⌜x⌝ₜ.size)
      ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
      ?step_time ?check_time ?stop_time ?step_pos ?stop_pos).mono ?time (Dominated.refl _)
  case equation =>
    rintro ⟨n, xs⟩
    cases xs with
    | nil => simp [lookupContinues]
    | cons a xs =>
      by_cases hn : n = 0
      · simp [lookupContinues, hn]
      · have hbits : n.bits ≠ [] := by
          intro h; have := BitList.toNat_bits n; simp [h, BitList.toNat] at this; omega
        simp [lookupContinues, lookupStep, List.getElem?_cons, hn, hbits, Nat.pred_eq_sub_one]
  case initial => exact fun _ => ⟨le_rfl, le_rfl, rfl⟩
  case next_state =>
    rintro x ⟨m, ys⟩ hi ht
    cases ys with
    | nil => simp [lookupContinues] at ht
    | cons a ys =>
      have hm : m ≠ 0 := by intro hm; subst m; simp [lookupContinues] at ht
      refine ⟨(Nat.length_bits_le_length_bits m.pred_le).trans hi.1, ?_, ?_⟩
      · exact (show ⌜ys⌝ₜ.size ≤ ⌜a :: ys⌝ₜ.size by simp).trans hi.2.1
      · simpa [lookupStep, List.getElem?_cons, hm, Nat.pred_eq_sub_one] using hi.2.2
  case decreases =>
    rintro x ⟨m, ys⟩ hi ht
    cases ys <;> simp_all [lookupContinues, lookupStep]
  case input_size => exact lookup_size
  case check_peak => exact lookup_size
  case step_peak => exact lookup_size
  case stop_peak => exact lookup_size
  case step_time => have := lookup_size (α := α); dominated
  case check_time => exact Dominated.one fun _ => Tree.size_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Tree.size_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time => dominated

/-- Look an index up in a list. -/
theorem _root_.List.hasProgramIn_getElem? {γ : Type*} [UniqueEncoding Tree γ] :
    HasProgramIn (fun p : List γ × ℕ => p.1[p.2]?)
      (fun v => (do let w ← Value.right v; let z ← Value.left v; Value.pair w z) >>= programLookup)
      IsO(fun p => ⌜p⌝ₜ.size ^ 2) IsO(fun p => ⌜p⌝ₜ.size) := by
  refine HasProgramInO.toHasProgramIn ?_
  refine ((Prod.hasProgramIn_snd.toHasProgramInO.pair Prod.hasProgramIn_fst.toHasProgramInO).comp
    hasProgramIn_lookup.toHasProgramInO).mono ?_ ?_ <;>
    dominated

attribute [program] List.hasProgramIn_getElem?

/-- The code of an optional value's content, or the empty tree. -/
def someValue {β : Type*} [UniqueEncoding Tree β] : Option β → Tree
  | none => .nil
  | some a => ⌜a⌝ₜ

/-- Read the value of a known successful optional result. -/
theorem hasProgramIn_someValue {β : Type*} [UniqueEncoding Tree β] :
    HasProgramIn (someValue (β := β)) hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programSomeValue
  fill_hole program in source_fun_prop

attribute [program] hasProgramIn_someValue

/-- An entry of a vector is read from the list of its entries at its index. -/
theorem encode_finVector_get_eq_someValue {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : FinVector α n) (i : Fin n) : ⌜v.get i⌝ₜ = ⌜someValue v.toList[i.val]?⌝ₜ := by
  simp [someValue]

-- After specific views, which avoid reading the whole vector.
attribute [source_view low] encode_finVector_get_eq_someValue

/-- Whether the counter of the range loop, read through its binary digits, is nonzero. -/
def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

/-- Decrease the counter by one and push the new counter onto the accumulated list. -/
def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

theorem hasProgramIn_rangeContinues :
    HasProgramIn rangeContinues hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRangeContinues
  fill_hole program in source_fun_prop

theorem hasProgramIn_rangeStep :
    HasProgramIn rangeStep hole(⊢ program) IsO(fun x => ⌜x.1⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRangeStep
  have := Nat.hasProgramIn_pred.toHasProgramInO.size_encode.comp (fun x : ℕ × List ℕ => x.1)
  fill_hole program in source_fun_prop

/-- The range loop as a source function: `List.range` of the counter followed by the accumulated
list; `List.range` is the case of an empty list. -/
def rangeLoop (x : ℕ × List ℕ) := List.range x.1 ++ x.2

/-- The invariant of the range loop: a reached state has a counter no larger than the input's and
the same range of the counter followed by the accumulated list. -/
def rangeInvariant (x y : ℕ × List ℕ) :=
  y.1 ≤ x.1 ∧ List.range y.1 ++ y.2 = List.range x.1 ++ x.2

theorem range_size :
    Dominated (fun z : {p : (ℕ × List ℕ) × (ℕ × List ℕ) // rangeInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => (z.1.1.1 + 1) ^ 2 + ⌜z.1.1.2⌝ₜ.size) := by
  apply (((Dominated.refl (fun z :
    {p : (ℕ × List ℕ) × (ℕ × List ℕ) // rangeInvariant p.1 p.2} =>
      (z.1.1.1 + 1) ^ 2)).const_mul_left 10).add (Dominated.refl _)).mono_left
  intro z
  obtain ⟨⟨x, y⟩, hi⟩ := z
  have hn := size_encode_nat_le y.1
  have hr := size_encode_range_le x.1
  have hx := size_encode_list_append (List.range x.1) x.2
  have hy := size_encode_list_append (List.range y.1) y.2
  have he := congrArg (fun z : List ℕ => ⌜z⌝ₜ.size) hi.2
  have hp := Tree.size_pos ⌜List.range y.1⌝ₜ
  have hle := hi.1
  rcases y with ⟨n, acc⟩
  dsimp only at *
  simp only [size_encode_prod]
  nlinarith

theorem hasProgramIn_rangeLoop : HasProgramIn rangeLoop hole(⊢ program) IsO(fun x => (x.1 + 1) ^ 2)
    IsO(fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size) := by
  abstract_hole program using programRangeLoop
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    refine (HasProgramInO.tail_loop hasProgramIn_rangeContinues.toHasProgramInO
      hasProgramIn_rangeStep.toHasProgramInO
      Prod.hasProgramIn_snd.toHasProgramInO rangeInvariant Prod.fst (fun x => x.1 + 1) (fun _ => 1)
      (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size)
      ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
      ?step_time ?check_time ?stop_time ?step_pos ?stop_pos).mono ?time (Dominated.refl _)
  case equation =>
    rintro ⟨n, xs⟩
    cases n with
    | zero => simp [rangeLoop, rangeContinues]
    | succ n =>
      have hbits : (n + 1).bits ≠ [] := by
        intro h; have := BitList.toNat_bits (n + 1); simp [h, BitList.toNat] at this
      simp [rangeLoop, rangeContinues, rangeStep, List.range_succ, List.append_assoc, hbits]
  case initial => exact fun _ => ⟨le_rfl, rfl⟩
  case next_state =>
    rintro x ⟨n, acc⟩ hi ht
    have hn : n ≠ 0 := by intro h; subst n; simp [rangeContinues] at ht
    refine ⟨(Nat.pred_le n).trans hi.1, ?_⟩
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
    simpa [rangeStep, List.range_succ, List.append_assoc] using hi.2
  case decreases =>
    rintro x ⟨n, acc⟩ hi ht
    have hn : n ≠ 0 := by intro h; subst n; simp [rangeContinues] at ht
    exact Nat.pred_lt hn
  case input_size => exact range_size
  case check_peak => exact range_size
  case step_peak => exact range_size
  case stop_peak => exact range_size
  case step_time => dominated [rangeInvariant]
  case check_time => exact Dominated.one fun _ => Nat.succ_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Nat.succ_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time => dominated

/-- Enumeration depends on the numerical length, not only its binary encoding size. -/
theorem _root_.List.hasProgramIn_range :
    HasProgramIn List.range hole(⊢ program) IsO(fun n => (n + 1) ^ 2)
      IsO(fun n => (n + 1) ^ 2) := by
  abstract_hole program using programRange
  let hr := hasProgramIn_rangeLoop
  fill_hole program in source_fun_prop via (fun n => rangeLoop (n, []))
  case source_eq => funext n; simp [rangeLoop]

attribute [program] List.hasProgramIn_range

theorem hasProgramIn_lengthStep {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (fun x : ℕ × α => x.1 + 1) hole(⊢ program)
      IsO(fun x => ⌜x.1⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLengthStep
  fill_hole program in source_fun_prop

theorem hasProgramIn_lengthInitial {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (fun xs : List α => (0, xs)) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programLengthInitial
  fill_hole program in source_fun_prop

/-- Count with the existing binary successor along a structural fold. -/
theorem _root_.List.hasProgramIn_length {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.length : List α → ℕ) hole(⊢ program) IsO(fun xs => ⌜xs⌝ₜ.size ^ 2)
      IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programLength
  refine HasProgramInO.toHasProgramIn ?_
  let I (xs rest : List α) (acc : ℕ) :=
    acc + rest.length ≤ xs.length ∧ ⌜rest⌝ₜ.size ≤ ⌜xs⌝ₜ.size
  have hs : Dominated (fun z : {z : List α × List α × ℕ // I z.1 z.2.1 z.2.2} =>
      ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
    apply Dominated.of_le_mul 7
    rintro ⟨⟨xs, rest, acc⟩, ha, hr⟩
    have hacc := size_encode_nat_le acc
    have hlen := length_le_codeSize xs
    have hpos := Tree.size_pos ⌜xs⌝ₜ
    change acc + rest.length ≤ xs.length at ha
    change ⌜rest⌝ₜ.size ≤ ⌜xs⌝ₜ.size at hr
    simp only [size_encode_prod]
    omega
  have ht : Dominated
      (fun z : {z : List α × α × List α × ℕ // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        ⌜z.1.2.2.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
    apply Dominated.of_le_mul 5
    intro z
    have hacc := size_encode_nat_le z.1.2.2.2
    have hlen := length_le_codeSize z.1.1
    have hpos := Tree.size_pos ⌜z.1.1⌝ₜ
    have hi := z.2.1
    omega
  have hp : Dominated
      (fun z : {z : List α × α × List α × ℕ // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        ⌜(z.1.2.2.2, z.1.2.1)⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) :=
    (hs.comp (fun z : {z : List α × α × List α × ℕ //
        I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
          ⟨(z.1.1, z.1.2.1 :: z.1.2.2.1, z.1.2.2.2), z.2⟩)).mono_left
      (fun z => by simp only [Function.comp_apply, size_encode_prod, encode_list_cons]; omega)
  have hfold := Dominated.foldl_of_invariant (f := fun _ n (_ : α) => n + 1)
    (t := fun _ x => ⌜x.1⌝ₜ.size) (p := fun _ x => ⌜x⌝ₜ.size) I (fun xs => xs) (fun _ => 0)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) (fun _ => ⟨by simp, le_rfl⟩)
    (by
      intro xs a rest acc hi
      refine ⟨by have := hi.1; simp only [List.length_cons] at *; omega, ?_⟩
      exact (show ⌜rest⌝ₜ.size ≤ ⌜a :: rest⌝ₜ.size by simp).trans hi.2)
    hs ht hp
  obtain ⟨htime, hpeak⟩ := hfold
  obtain ⟨-, hpeak⟩ := Dominated.max_iff.mp hpeak
  fill_hole program in
    refine (HasProgramInO.of_encode (by simp) (hasProgramIn_lengthInitial.toHasProgramInO.comp
      (hasProgramIn_lengthStep.toHasProgramInO.foldl (f := fun n (_ : α) => n + 1)))).mono ?_ ?_
  all_goals dominated

attribute [program] List.hasProgramIn_length

/-- The conjunction of a list of Booleans, by a left fold without short-circuiting. -/
theorem _root_.List.hasProgramIn_and : HasProgramIn List.and hole(⊢ program)
    IsO(fun bs => ⌜bs⌝ₜ.size) IsO(fun bs => ⌜bs⌝ₜ.size) := by
  abstract_hole program using programAnd
  fill_hole program in
    source_fun_prop via (fun bs : List Bool => bs.foldl (fun b x => b && x) true)
  case source_eq =>
    funext bs
    suffices ∀ c, (c && bs.and) = bs.foldl (fun b x => b && x) c by simpa using this true
    induction bs with
    | nil => simp
    | cons x bs ih => intro c; simp [← ih, Bool.and_assoc]

/-- The disjunction of a list of Booleans, by a left fold without short-circuiting. -/
theorem _root_.List.hasProgramIn_or : HasProgramIn List.or hole(⊢ program)
    IsO(fun bs => ⌜bs⌝ₜ.size) IsO(fun bs => ⌜bs⌝ₜ.size) := by
  abstract_hole program using programOr
  fill_hole program in
    source_fun_prop via (fun bs : List Bool => bs.foldl (fun b x => b || x) false)
  case source_eq =>
    funext bs
    suffices ∀ c, (c || bs.or) = bs.foldl (fun b x => b || x) c by simpa using this false
    induction bs with
    | nil => simp
    | cons x bs ih => intro c; simp [← ih, Bool.or_assoc]

attribute [program] List.hasProgramIn_and List.hasProgramIn_or

/-- A check of every element of a list is computed as the conjunction of the mapped list: the
predicate is a callback of the map, so it may capture values. -/
@[source_view] theorem encode_list_all {α : Type*} (xs : List α) (p : α → Bool) :
    ⌜xs.all p⌝ₜ = ⌜(xs.map p).and⌝ₜ := by
  simp [List.and, List.all_map]

/-- A check of some element of a list is computed as the disjunction of the mapped list. -/
@[source_view] theorem encode_list_any {α : Type*} (xs : List α) (p : α → Bool) :
    ⌜xs.any p⌝ₜ = ⌜(xs.map p).or⌝ₜ := by
  simp [List.or, List.any_map]

/-- Membership is computed as a check of some element with `==`, for any type whose `==` has an
implementation. `List.contains` is reducible to `List.elem`. -/
@[source_view] theorem encode_list_elem {α : Type*} [BEq α] (a : α) (xs : List α) :
    ⌜xs.elem a⌝ₜ = ⌜xs.any (a == ·)⌝ₜ := by
  rw [List.elem_eq_contains, List.contains_eq_any_beq]

/-- The arguments of reading a vector of indices through another vector. -/
abbrev FinVectorLookupInput := Σ n, Σ k, Σ m, FinVector (Fin k) n × FinVector (Fin m) k

/-- Read a vector of indices through another vector. -/
theorem hasProgramIn_finVectorLookup :
    HasProgramIn (fun x : FinVectorLookupInput => x.2.2.2.1.map x.2.2.2.2.get) hole(⊢ program)
      IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programFinVectorLookup
  fill_hole program in source_fun_prop

/-- Read a vector of indices through another vector, with the closed growth of the stored lookup.
Callbacks inside a `match` can use this rule when `dominated` compares branch costs only pointwise
and does not bound the sum of a map directly. -/
theorem Internal.HasProgramInO.finVector_map_get {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → FinVector (Fin (k e)) (n e)}
    {g : (e : ρ) → FinVector (Fin (m e)) (k e)} {q : Value → Code Value} {t p : ρ → ℕ}
    (h : HasProgramInO (fun e => (⟨n e, k e, m e, f e, g e⟩ : FinVectorLookupInput)) q t p) :
    HasProgramInO (fun e => (f e).map (g e).get) (fun v => q v >>= programFinVectorLookup)
      (fun e => t e + ⌜(⟨n e, k e, m e, f e, g e⟩ : FinVectorLookupInput)⌝ₜ.size ^ 3)
      (fun e => max (p e) (⌜(⟨n e, k e, m e, f e, g e⟩ : FinVectorLookupInput)⌝ₜ.size ^ 2)) :=
  h.comp_dependent hasProgramIn_finVectorLookup.toHasProgramInO

end Complexity.TreeProgram.Source
