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

def lookupContinues {α : Type*} (x : ℕ × List α) : Bool :=
  match x.2 with | [] => false | _ :: _ => !x.1.bits.isEmpty

def lookupStep {α : Type*} (x : ℕ × List α) := (x.1.pred, x.2.tail)

theorem hasProgram_lookupContinues {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (lookupContinues (α := α)) hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupContinues
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_lookupStep {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (lookupStep (α := α)) hole(⊢ program)
      (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupStep
  have := Nat.hasProgram_pred.size_encode.comp (fun x : ℕ × List α => x.1)
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_lookupFinish {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (fun x : ℕ × List α => x.2.head?) hole(⊢ program)
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookupFinish
  fill_hole program in source_fun_prop
  all_goals dominated

def lookupInvariant {α : Type*} [UniqueEncoding Tree α] (x y : ℕ × List α) :=
  y.1.bits.length ≤ x.1.bits.length ∧ ⌜y.2⌝ₜ.size ≤ ⌜x.2⌝ₜ.size ∧ y.2[y.1]? = x.2[x.1]?

theorem lookup_size {α : Type*} [UniqueEncoding Tree α] :
    Dominated (fun z : {p : (ℕ × List α) × (ℕ × List α) // lookupInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [lookupInvariant, size_encode_nat_le_length_bits]

/-- Indexed lookup uses selected callbacks and one invariant-family growth specification. -/
theorem hasProgram_lookup {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (fun x : ℕ × List α => x.2[x.1]?) hole(⊢ program) (fun x => ⌜x⌝ₜ.size ^ 2)
      (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLookup
  fill_hole program in
    refine (HasProgram.tailLoop hasProgram_lookupContinues hasProgram_lookupStep
      hasProgram_lookupFinish lookupInvariant
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
  case step_time => exact lookup_size.mono_left fun z => size_encode_fst_le z.1.2
  case check_time => exact Dominated.one fun _ => Tree.size_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Tree.size_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time => dominated

theorem encode_option_codes {γ : Type*} [UniqueEncoding Tree γ] (o : Option γ) :
    ⌜o.map (encode Tree)⌝ₜ = ⌜o⌝ₜ := by
  cases o <;> simp only [Option.map_none, Option.map_some, encode_option_none, encode_option_some,
    encode_prod, Tree.encode_self]

/-- Look an index up in a list, on the codes of its entries. -/
theorem HasProgram.getElem? {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {f : (x : α) → List (β x)} {i : α → ℕ}
    {qf qi : Value → Code Value} {tf pf ti pi : α → ℕ}
    (hf : HasProgram f qf tf pf) (hi : HasProgram i qi ti pi) :
    HasProgram (fun x => (f x)[i x]?) hole(qf, qi ⊢ program)
      (fun x => ti x + (tf x + 1) + ⌜(i x, f x)⌝ₜ.size ^ 2)
      (fun x => max (max (pi x) (max (pf x) ⌜(i x, f x)⌝ₜ.size)) ⌜(i x, f x)⌝ₜ.size) := by
  fill_hole program in
    exact (((hi.pair hf.listCodes).comp hasProgram_lookup).ofEncode fun x => by
        simp only [Function.comp_apply, List.getElem?_map, encode_option_codes]).mono
      (Dominated.of_le fun x => by simp only [size_encode_prod, encode_list_codes, le_refl])
      (Dominated.of_le fun x => by simp only [size_encode_prod, encode_list_codes, le_refl])

attribute [scoped fun_prop] HasProgram.getElem?

/-- The code of a computed value is the value's own result. -/
theorem HasProgram.encodeTree {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {v : (x : α) → β x} {q : Value → Code Value} {t p : α → ℕ}
    (hv : HasProgram v q t p) : HasProgram (fun x => ⌜v x⌝ₜ) q t p :=
  hv.ofEncode fun _ => Tree.encode_self _

attribute [scoped fun_prop] HasProgram.encodeTree

/-- Reading a represented table reuses its code; construction remains a separate premise. -/
theorem HasProgram.ofFn {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {n : α → ℕ} {f : (x : α) → Fin (n x) → β x}
    {q : Value → Code Value} {t p : α → ℕ} (hf : HasProgram (fun x => ⌜f x⌝ₜ) q t p) :
    HasProgram (fun x => List.ofFn (f x)) q t p :=
  .ofEncode (g := fun x => ⌜f x⌝ₜ) (fun _ => rfl) hf

attribute [scoped fun_prop] HasProgram.ofFn

/-- Read the value of a known successful optional result. -/
theorem hasProgram_someValue {β : Type*} [UniqueEncoding Tree β] :
    HasProgram (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ)
      hole(⊢ program)
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programSomeValue
  fill_hole program in source_fun_prop
  all_goals dominated

/-- Removing a known successful result adds one fixed operation and retains the selected call. -/
theorem HasProgram.ofSome {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {f : (x : α) → β x} {g : (x : α) → Option (β x)}
    {q : Value → Code Value} {t p : α → ℕ} (hg : HasProgram g q t p)
    (hfg : ∀ x, g x = some (f x)) :
    HasProgram f (fun v => q v >>= programSomeValue) (fun x => t x + 1)
      (fun x => max (p x) ⌜g x⌝ₜ.size) :=
  (((hg.ofEncode (f := fun x => (g x).map (encode Tree)) fun x => encode_option_codes _).comp
    hasProgram_someValue).ofEncode fun x => by simp [hfg]).mono
    (Dominated.refl _) (Dominated.of_le fun x => by simp only [encode_option_codes, le_refl])

def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

theorem hasProgram_rangeContinues :
    HasProgram rangeContinues hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRangeContinues
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_rangeStep :
    HasProgram rangeStep hole(⊢ program) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRangeStep
  have := Nat.hasProgram_pred.size_encode.comp (fun x : ℕ × List ℕ => x.1)
  fill_hole program in source_fun_prop
  all_goals dominated

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

theorem hasProgram_rangeLoop : HasProgram rangeLoop hole(⊢ program) (fun x => (x.1 + 1) ^ 2)
    (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size) := by
  abstract_hole program using programRangeLoop
  fill_hole program in
    refine (HasProgram.tailLoop hasProgram_rangeContinues hasProgram_rangeStep
      Prod.hasProgram_snd rangeInvariant Prod.fst (fun x => x.1 + 1) (fun _ => 1)
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
theorem _root_.List.hasProgram_range :
    HasProgram List.range hole(⊢ program) (fun n => (n + 1) ^ 2) (fun n => (n + 1) ^ 2) := by
  abstract_hole program using programRange
  let hr := hasProgram_rangeLoop
  fill_hole program in source_fun_prop via (fun n => rangeLoop (n, []))
  case source_eq => funext n; simp [rangeLoop]
  all_goals dominated

attribute [scoped fun_prop] List.hasProgram_range

theorem hasProgram_lengthStep {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (fun x : ℕ × α => x.1 + 1) hole(⊢ program)
      (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLengthStep
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_lengthInitial {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (fun xs : List α => (0, xs)) hole(⊢ program)
      (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programLengthInitial
  fill_hole program in source_fun_prop
  all_goals dominated

/-- Count with the existing binary successor along a structural fold. -/
theorem _root_.List.hasProgram_length {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (List.length : List α → ℕ) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size ^ 2)
      (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programLength
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
  have hfold := Dominated.foldl_of_invariant (f := fun n (_ : α) => n + 1)
    (t := fun x => ⌜x.1⌝ₜ.size) (p := fun x => ⌜x⌝ₜ.size) I (fun xs => xs) (fun _ => 0)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) (fun _ => ⟨by simp, le_rfl⟩)
    (by
      intro xs a rest acc hi
      refine ⟨by have := hi.1; simp only [List.length_cons] at *; omega, ?_⟩
      exact (show ⌜rest⌝ₜ.size ≤ ⌜a :: rest⌝ₜ.size by simp).trans hi.2)
    hs ht hp
  obtain ⟨htime, hpeak⟩ := hfold
  obtain ⟨-, hpeak⟩ := Dominated.max_iff.mp hpeak
  fill_hole program in
    refine (HasProgram.ofEncode (by simp) (hasProgram_lengthInitial.comp
      ((hasProgram_lengthStep (α := α)).foldl (f := fun n (_ : α) => n + 1)))).mono ?_ ?_
  all_goals dominated

attribute [scoped fun_prop] List.hasProgram_length

/-- Construct a represented tuple using one selected callback for every environment and index.
Tabulation sums the callback growth; one coefficient covers every environment and index. -/
theorem HasProgram.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [instβ : ∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {qn qf : Value → Code Value} {tn pn : ρ → ℕ}
    {tf pf : (Σ e, Fin (n e)) → ℕ} (hn : HasProgram n qn tn pn)
    (hf : HasProgram (fun p : Σ e, Fin (n e) => f p.1 p.2) qf tf pf) :
    HasProgram (fun e => ⌜f e⌝ₜ) hole(qn, qf ⊢ program)
      (fun e => (tn e + (n e + 1) ^ 2 + 1) +
        (((List.finRange (n e)).map (fun i => tf ⟨e, i⟩)).sum + n e + 1))
      (fun e => max (max (pn e) ((n e + 1) ^ 2))
        (max ⌜(e, List.range (n e))⌝ₜ.size (max (⌜f e⌝ₜ.size + 1)
          ((List.finRange (n e)).foldr (fun i s => max (pf ⟨e, i⟩) s) 0)))) := by
  have heq (e : ρ) : ⌜(⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))⌝ₜ =
      ⌜(e, List.range (n e))⌝ₜ := by simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  have he := HasProgram.ofEncode heq
    (HasProgram.identity.pair (hn.comp List.hasProgram_range))
  fill_hole program in
    refine (HasProgram.ofEncode (g := fun e => (List.finRange (n e)).map (f e))
      (fun e => by rw [← List.ofFn_eq_map, Tree.encode_self, encode_fin_function])
      (he.mapDependentWith (f := f) hf)).mono ?_ ?_
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
attribute [scoped source_fallback] Complexity.TreeProgram.Source.HasProgram.finFunction

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``Complexity.TreeProgram.Source.HasProgram.finFunction .scoped 50

end tabulate

namespace Complexity.TreeProgram.Source

/-- Reading a represented table evaluates the index and the table once, then looks the index up
in the table's code. -/
theorem HasProgram.finApply {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)}
    {qf qi : Value → Code Value} {tf pf ti pi : ρ → ℕ}
    (hf : HasProgram (fun e => ⌜f e⌝ₜ) qf tf pf)
    (hi : HasProgram (fun e => (i e).val) qi ti pi) :
    HasProgram (fun e => f e (i e)) hole(qf, qi ⊢ program)
      (fun e => ti e + (tf e + 1) + ⌜(i e, f e)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜(i e, f e)⌝ₜ.size)) := by
  have ht : HasProgram (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) qf tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  fill_hole program in
    refine ((((hi.pair ht).comp hasProgram_lookup).ofSome (by intro e; simp)).ofEncode
      (fun e => (Tree.encode_self _).symm)).mono ?_ ?_
  · apply Dominated.of_le
    intro e
    simp only [size_encode_prod, encode_fin_function_codes, encode_fin]
    exact le_rfl
  · apply Dominated.of_le
    intro e
    have hv := size_encode_fin_apply_le (f e) (i e)
    have hi := Tree.size_pos ⌜(i e).val⌝ₜ
    simp only [Function.comp_apply, List.getElem?_ofFn, Fin.isLt, dite_true, Fin.eta,
      encode_option_some, size_encode_prod, Tree.encode_self, size_encode_unit,
      encode_fin_function_codes, encode_fin]
    omega

/-- A one-element list of an encoded value. -/
theorem hasProgram_singleton : HasProgram (fun t : Tree => [t]) hole(⊢ program) (fun _ => 1)
    (fun t => ⌜t⌝ₜ.size) := by
  abstract_hole program using programSingleton
  fill_hole program in source_fun_prop
  all_goals dominated

theorem _root_.List.hasProgram_tail {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (List.tail : List α → List α) hole(⊢ program)
      (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programTail
  fill_hole program in source_fun_prop
  all_goals dominated

attribute [scoped fun_prop] List.hasProgram_tail

section Index

/-! Operations on indices; an index is stored as its value. -/

variable {ρ : Type*} [UniqueEncoding Tree ρ] {k m : ρ → ℕ} {i : (e : ρ) → Fin (k e)}
  {q : Value → Code Value} {t p : ρ → ℕ}

/-- The last index is stored as its value. -/
theorem HasProgram.finLast (hk : HasProgram k q t p) :
    HasProgram (fun e => Fin.last (k e)) q t p :=
  hk.ofEncode fun _ => by rw [encode_fin, Fin.val_last]

/-- Casting an index up keeps its value. -/
theorem HasProgram.finCastSucc (hi : HasProgram i q t p) :
    HasProgram (fun e => (i e).castSucc) q t p :=
  .ofEncode (f := fun e => (i e).castSucc) (g := i) (fun _ => rfl) hi

/-- Casting an index into a longer range keeps its value. -/
theorem HasProgram.finCastAdd (hi : HasProgram i q t p) :
    HasProgram (fun e => Fin.castAdd (m e) (i e)) q t p :=
  .ofEncode (f := fun e => Fin.castAdd (m e) (i e)) (g := i) (fun _ => rfl) hi

/-- Shifting an index is an addition of its value. -/
theorem HasProgram.finNatAdd (h : HasProgram (fun e => m e + (i e).val) q t p) :
    HasProgram (fun e => Fin.natAdd (m e) (i e)) q t p :=
  .ofEncode (f := fun e => Fin.natAdd (m e) (i e)) (g := fun e => m e + (i e).val)
    (fun _ => rfl) h

/-- The value of an index is stored as the index. -/
theorem HasProgram.finVal (hi : HasProgram i q t p) :
    HasProgram (fun e => (i e).val) q t p :=
  .ofEncode (f := fun e => (i e).val) (g := i) (fun _ => rfl) hi

/-- The next index is a successor of the value. -/
theorem HasProgram.finSucc (h : HasProgram (fun e => (i e).val + 1) q t p) :
    HasProgram (fun e => (i e).succ) q t p :=
  .ofEncode (f := fun e => (i e).succ) (g := fun e => (i e).val + 1) (fun _ => rfl) h

/-- The first index of a nonempty range is stored as zero, the empty tree. -/
theorem HasProgram.finZero :
    HasProgram (fun e => (0 : Fin (k e + 1))) (fun _ => pure .nil) (fun _ => 0) (fun _ => 0) :=
  .ofEncode (f := fun e => (0 : Fin (k e + 1))) (g := fun _ => ())
    (fun e => by rw [encode_fin, encode_unit]; simp; rfl) HasProgram.unit

attribute [scoped fun_prop] HasProgram.finVal HasProgram.finSucc HasProgram.finZero
  HasProgram.finCastSucc HasProgram.finCastAdd HasProgram.finNatAdd HasProgram.finLast

end Index

/-- Extend a represented table without re-enumerating its indices. -/
theorem HasProgram.finSnoc {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {a : (e : ρ) → α e} {qf qa : Value → Code Value}
    {tf pf ta pa : ρ → ℕ} (hf : HasProgram (fun e => ⌜f e⌝ₜ) qf tf pf)
    (ha : HasProgram a qa ta pa) :
    HasProgram (fun e => ⌜Fin.snoc (α := fun _ => α e) (f e) (a e)⌝ₜ) hole(qf, qa ⊢ program)
      (fun e => tf e + ta e + n e + 1)
      (fun e => max (pf e) (max (pa e) (⌜f e⌝ₜ.size + ⌜a e⌝ₜ.size))) := by
  have ht : HasProgram (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) qf tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  have hc : HasProgram (fun e => ⌜a e⌝ₜ) qa ta pa := ha.ofEncode fun e => Tree.encode_self _
  fill_hole program in
    refine (HasProgram.ofEncode ?_ (ht.append (hc.comp hasProgram_singleton))).mono ?_ ?_
  · intro e
    rw [Tree.encode_self, encode_fin_snoc]
    simpa only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
      Function.comp_def] using
      (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
        (List.ofFn (f e) ++ [a e])).symm
  · apply Dominated.of_le_mul 2
    intro e
    simp only [List.length_ofFn]
    omega
  · apply Dominated.of_le_mul 3
    intro e
    have := Tree.size_pos ⌜f e⌝ₜ
    have := Tree.size_pos ⌜a e⌝ₜ
    simp only [Function.comp_apply, Tree.encode_self, encode_fin_function_codes,
      encode_list_cons, encode_list_nil, size_encode_prod, size_encode_unit, max_le_iff]
    omega

/-- Concatenate represented tables using the existing list append implementation. -/
theorem HasProgram.finAppend {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e}
    {g : (e : ρ) → Fin (m e) → α e} {qf qg : Value → Code Value} {tf pf tg pg : ρ → ℕ}
    (hf : HasProgram (fun e => ⌜f e⌝ₜ) qf tf pf) (hg : HasProgram (fun e => ⌜g e⌝ₜ) qg tg pg) :
    HasProgram (fun e => ⌜Fin.append (f e) (g e)⌝ₜ)
      (fun v => do let w ← qf v; let z ← qg v; List.Code.append w z)
      (fun e => tf e + (tg e + (n e + 1)))
      (fun e => max (pf e) (max (pg e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))) := by
  have hf' : HasProgram (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) qf tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  have hg' : HasProgram (fun e => List.ofFn (fun i => ⌜g e i⌝ₜ)) qg tg pg :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hg
  refine (HasProgram.ofEncode
    (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ) ++ List.ofFn (fun i => ⌜g e i⌝ₜ))
    ?_ (hf'.append hg')).mono (Dominated.of_le fun e => by simp only [List.length_ofFn, le_refl])
      (Dominated.of_le fun e => by simp only [encode_fin_function_codes, le_refl])
  intro e
  rw [Tree.encode_self, encode_fin_function, List.ofFn_fin_append]
  simpa only [List.map_append, List.map_ofFn, Function.comp_def] using
    (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
      (List.ofFn (f e) ++ List.ofFn (g e))).symm

/-- Casting the entries of a table of indices up keeps its code. -/
theorem HasProgram.finCastSuccComp {ρ : Type*} [UniqueEncoding Tree ρ] {n k : ρ → ℕ}
    {f : (e : ρ) → Fin (n e) → Fin (k e)} {q : Value → Code Value} {t p : ρ → ℕ}
    (hf : HasProgram (fun e => ⌜f e⌝ₜ) q t p) :
    HasProgram (fun e => ⌜Fin.castSucc ∘ f e⌝ₜ) q t p :=
  hf.ofEncode fun e => by rw [Tree.encode_self, Tree.encode_self, encode_fin_castSucc]

/-- Erasing the bounds of a table of indices keeps its code. -/
theorem HasProgram.finValComp {ρ : Type*} [UniqueEncoding Tree ρ] {n k : ρ → ℕ}
    {f : (e : ρ) → Fin (n e) → Fin (k e)} {q : Value → Code Value} {t p : ρ → ℕ}
    (hf : HasProgram (fun e => ⌜f e⌝ₜ) q t p) :
    HasProgram (fun e => ⌜Fin.val ∘ f e⌝ₜ) q t p :=
  hf.ofEncode fun e => by
    rw [Tree.encode_self, Tree.encode_self]
    exact encode_fin_function_congr _ _ fun _ => rfl

-- Known operations reuse their certificates before unfolding.
attribute [scoped fun_prop] HasProgram.finSnoc HasProgram.finAppend
  HasProgram.finCastSuccComp HasProgram.finValComp

abbrev FinCompInput := Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)

theorem hasProgram_finCompCount :
    HasProgram (fun x : FinCompInput => x.1) hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programFinCompCount
  fill_hole program in source_fun_prop
  all_goals dominated

theorem hasProgram_finCompStep :
    HasProgram (fun z : Σ x : FinCompInput, Fin x.1 => z.1.2.2.2.2 (z.1.2.2.2.1 z.2))
      hole(⊢ program)
      (fun z => ⌜z.1⌝ₜ.size ^ 2) (fun z => ⌜z.1⌝ₜ.size ^ 2) := by
  abstract_hole program using programFinCompStep
  fill_hole program in source_fun_prop
  all_goals dominated

/-- Stored table composition directly enumerates its selected lookup callback. -/
theorem hasProgram_finComp :
    HasProgram (fun x : FinCompInput => ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ) hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programFinComp
  fill_hole program in
    refine (HasProgram.finFunction (β := fun x : FinCompInput => Fin x.2.2.1)
      (instβ := fun _ => inferInstance) (n := fun x => x.1) (f := fun x => x.2.2.2.2 ∘ x.2.2.2.1)
      hasProgram_finCompCount hasProgram_finCompStep).mono ?_ ?_
  all_goals dominated

/-- Reuse the existing table-composition backend while retaining the caller's program. -/
theorem HasProgram.finComp {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)}
    {g : (e : ρ) → Fin (k e) → Fin (m e)} {q : Value → Code Value} {t p : ρ → ℕ}
    (h : HasProgram (fun e => (⟨n e, k e, m e, f e, g e⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m))) q t p) :
    HasProgram (fun e => ⌜g e ∘ f e⌝ₜ) (fun v => q v >>= programFinComp)
      (fun e => t e + ⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 3)
      (fun e => max (p e) (⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 2)) :=
  h.comp hasProgram_finComp

end Complexity.TreeProgram.Source
