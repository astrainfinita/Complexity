/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Iteration
public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for binary arithmetic and finite tables -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

theorem _root_.List.hasProgramIn_tail {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.tail : List α → List α) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programTail
  fill_hole program in source_fun_prop

attribute [scoped program] List.hasProgramIn_tail

def lookupContinues {α : Type*} (x : ℕ × List α) : Bool :=
  match x.2 with | [] => false | _ :: _ => !x.1.bits.isEmpty

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
      have hp : m.pred.bits.length ≤ m.bits.length := by
        simpa [Nat.pred_eq_sub_one] using BitList.length_decrement_le m.bits
      refine ⟨hp.trans hi.1, ?_, ?_⟩
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

attribute [scoped program] List.hasProgramIn_getElem?

/-- The code of an optional value's content, or the empty tree. -/
def someValue {β : Type*} [UniqueEncoding Tree β] : Option β → Tree
  | none => .nil
  | some a => ⌜a⌝ₜ

/-- Read the value of a known successful optional result. -/
theorem hasProgramIn_someValue {β : Type*} [UniqueEncoding Tree β] :
    HasProgramIn (someValue (β := β)) hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programSomeValue
  fill_hole program in source_fun_prop

attribute [scoped program] hasProgramIn_someValue

/-! A table has the code of its vector (`encode_fin_function_vector`), and a vector that of its
list (`encode_vector`). The search computes a table through them, by these equations and the list
rules; the vector of a stored table is the table. -/

theorem _root_.Vector.ofFn_fin_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) :
    Vector.ofFn (Fin.snoc f a) = (Vector.ofFn f).push a := by
  rw [Vector.ofFn_succ]
  simp [Fin.snoc]

theorem _root_.Vector.ofFn_fin_append {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    Vector.ofFn (Fin.append f g) = Vector.ofFn f ++ Vector.ofFn g := by
  rw [Vector.ofFn_add]
  simp

/-- `Fin.append` is reducible, so the search sees `Fin.addCases`. -/
theorem _root_.Vector.ofFn_addCases {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    Vector.ofFn (Fin.addCases (motive := fun _ => α) f g) = Vector.ofFn f ++ Vector.ofFn g :=
  Vector.ofFn_fin_append f g

/-! The search unfolds `Function.comp` as notation, so a table of converted entries is a function
literal. -/

/-- Casting the entries of a table of indices up keeps its code. -/
theorem encode_fun_castSucc {n k : ℕ} (f : Fin n → Fin k) : ⌜fun i => (f i).castSucc⌝ₜ = ⌜f⌝ₜ :=
  encode_fin_function_congr _ _ fun _ => rfl

/-- Erasing the bounds of the entries of a table of indices keeps its code. -/
theorem encode_fun_val {n k : ℕ} (f : Fin n → Fin k) : ⌜fun i => (f i).val⌝ₜ = ⌜f⌝ₜ :=
  encode_fin_function_congr _ _ fun _ => rfl

/-- An entry of a table is read from the list of entry codes at its index. The codes have one
type for every table, even when the entries' type depends on the input. -/
theorem encode_apply_eq_someValue {α : Type*} [UniqueEncoding Tree α] {n : ℕ} (f : Fin n → α)
    (i : Fin n) : ⌜f i⌝ₜ = ⌜someValue (List.ofFn fun j => ⌜f j⌝ₜ)[i.val]?⌝ₜ := by
  simp [someValue]

/-- Reading the list of a table at an index gives the entry. -/
@[dominated_simp] theorem _root_.List.getElem?_ofFn_val {α : Type*} {n : ℕ} (f : Fin n → α)
    (i : Fin n) : (List.ofFn f)[i.val]? = some (f i) := by
  simp

attribute [source_view] Vector.ofFn_fin_snoc Vector.ofFn_fin_append Vector.ofFn_addCases
  encode_fun_castSucc encode_fun_val
-- After the views, which compute an entry without reading the table.
attribute [source_view low] encode_apply_eq_someValue

def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

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

def rangeLoop (x : ℕ × List ℕ) := List.range x.1 ++ x.2

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

attribute [scoped program] List.hasProgramIn_range

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

attribute [scoped program] List.hasProgramIn_length

/-- Construct a represented tuple using one selected callback for every environment and index.
Tabulation sums the callback growth; one coefficient covers every environment and index. -/
theorem Internal.HasProgramInO.fin_function {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [instβ : ∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {qn qf : Value → Code Value} {tn pn : ρ → ℕ}
    {tf pf : (Σ e, Fin (n e)) → ℕ} (hn : HasProgramInO n qn tn pn)
    (hf : HasProgramInO (fun p : Σ e, Fin (n e) => f p.1 p.2) qf tf pf) :
    HasProgramInO (fun e => Vector.ofFn (f e)) hole(qn, qf ⊢ program)
      (fun e => (tn e + (n e + 1) ^ 2 + 1) +
        (((List.finRange (n e)).map (fun i => tf ⟨e, i⟩)).sum + n e + 1))
      (fun e => max (max (pn e) ((n e + 1) ^ 2))
        (max ⌜(e, List.range (n e))⌝ₜ.size (max (⌜f e⌝ₜ.size + 1)
          ((List.finRange (n e)).foldr (fun i s => max (pf ⟨e, i⟩) s) 0)))) := by
  have heq (e : ρ) : ⌜(⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))⌝ₜ =
      ⌜(e, List.range (n e))⌝ₜ := by simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  have he := HasProgramInO.of_encode heq
    (HasProgramInO.identity.pair (hn.comp List.hasProgramIn_range.toHasProgramInO))
  fill_hole program in
    refine (HasProgramInO.of_encode
      (fun e => by rw [encode_vector, Vector.toList_ofFn, List.ofFn_eq_map])
      (he.map_dependent_with hf)).mono ?_ ?_
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_add, List.length_finRange]
    omega
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_max, ← List.ofFn_eq_map, ← encode_fin_function, heq, id_eq]
    omega

end Complexity.TreeProgram.Source

namespace tabulate

-- Enumeration is an optional library rule, after stored-field extraction and lookup.
attribute [scoped source_fallback] Complexity.TreeProgram.Source.Internal.HasProgramInO.fin_function

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``Complexity.TreeProgram.Source.Internal.HasProgramInO.fin_function .scoped 50

end tabulate

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

abbrev FinCompInput := Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)

theorem hasProgramIn_finCompStep :
    HasProgramIn (fun z : Σ x : FinCompInput, Fin x.1 => z.1.2.2.2.2 (z.1.2.2.2.1 z.2))
      hole(⊢ program)
      IsO(fun z => ⌜z.1⌝ₜ.size ^ 2) IsO(fun z => ⌜z.1⌝ₜ.size ^ 2) := by
  abstract_hole program using programFinCompStep
  fill_hole program in source_fun_prop

/-- Stored table composition directly enumerates its selected lookup callback. -/
theorem hasProgramIn_finComp :
    HasProgramIn (fun x : FinCompInput => Vector.ofFn (x.2.2.2.2 ∘ x.2.2.2.1)) hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programFinComp
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    -- The entry encodings are a family over the environment, which the callback states only at
    -- `z.1`; unification cannot recover the family from there.
    refine (HasProgramInO.fin_function Sigma.hasProgramIn_fst.toHasProgramInO
      hasProgramIn_finCompStep.toHasProgramInO).mono ?_ ?_
  all_goals dominated

/-- Reuse the existing table-composition backend while retaining the caller's program. -/
theorem Internal.HasProgramInO.fin_comp {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)}
    {g : (e : ρ) → Fin (k e) → Fin (m e)} {q : Value → Code Value} {t p : ρ → ℕ}
    (h : HasProgramInO (fun e => (⟨n e, k e, m e, f e, g e⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m))) q t p) :
    HasProgramInO (fun e => Vector.ofFn (g e ∘ f e)) (fun v => q v >>= programFinComp)
      (fun e => t e + ⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 3)
      (fun e => max (p e) (⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 2)) :=
  h.comp_dependent hasProgramIn_finComp.toHasProgramInO

end Complexity.TreeProgram.Source
