/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Traverse
public import Complexity.Models.TreeMachine.Encoding
public import Complexity.Models.TuringMachine.Program.Specification.History
public import Complexity.Data.IntMemory.List

/-!
# Scanning one prefix-coded tree with a monadic program

The source and destination may be arbitrary work tapes. A third tape contains `some true` only at
zero and represents the number of pending subtrees by its head position. The invariant follows
prefixes of the tree code, so the suffix after the scanned tree is completely unconstrained.
-/

@[expose] public section

namespace Complexity.TreeMachine.Program

open TM Std.WP
open Controller (History)

variable {κ : Type} [DecidableEq κ] {zs : Array (Option Bool)}

/-- Consume one tree token, optionally appending it to the destination. -/
def scanToken (s d c : κ) (copy b : Bool) : TM.Action κ (Option Bool) Unit :=
  { TM.Program.idle (κ := κ) with
    work := fun i =>
      if i = s then (none, 1)
      else if i = d then if copy then (some (some b), 1) else (none, 0)
      else if i = c then (none, if b then 1 else -1)
      else (none, 0) }

/-- One tree-token iteration. The counter zero cell decides whether the tree is complete. -/
def scanBody (s d c : κ) (copy : Bool) : TM.Program κ (Option Bool) Bool := do
  let a ← TM.Program.read s
  TM.Program.act (scanToken s d c copy (decide (a = some true)))
  let a ← TM.Program.read c
  pure (decide (a = some true))

/-- Scan exactly one prefix-coded tree, using the counter head as a unary stack depth. -/
def scan (s d c : κ) (copy : Bool) : TM.Program κ (Option Bool) Unit :=
  TM.Program.repeatUntil (scanBody s d c copy)

/-- Destination contents after processing a prefix of the input tree. -/
def scanWord (copy : Bool) (ys : List (Option Bool)) (a : Tree) (n : ℕ) : List (Option Bool) :=
  if copy then ys ++ (code a).take n else ys

/-- The tape data after `n` tokens, preserving every unrelated field of the configuration. -/
@[simps -fullyApplied]
def scanCfg (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (p : ℕ) (ys : List (Option Bool)) (n : ℕ) : TM.Cfg κ (Option Bool) Unit zs :=
  { u with
    workTapes := Function.update u.workTapes d (IntMemory.ofList (scanWord copy ys a n))
    workPos := fun i =>
      if i = s then p + n
      else if i = d then (scanWord copy ys a n).length
      else if i = c then 1 + BitList.balance ((BitList.encodeTree a).take n)
      else u.workPos i }

private theorem scanWord_succ (copy : Bool) (ys : List (Option Bool)) (a : Tree) {n : ℕ}
    (hn : n < a.size) :
    scanWord copy ys a (n + 1) =
      if copy then scanWord copy ys a n ++ [some ((BitList.encodeTree a)[n]'(by simpa using hn))]
      else scanWord copy ys a n := by
  cases copy with
  | false => rfl
  | true =>
    simp only [scanWord, ↓reduceIte]
    rw [List.take_succ_eq_append_getElem (show n < (code a).length by simpa using hn)]
    simp [code, List.append_assoc]

private theorem balance_succ (a : Tree) {n : ℕ} (hn : n < a.size) :
    BitList.balance ((BitList.encodeTree a).take (n + 1)) =
      BitList.balance ((BitList.encodeTree a).take n) +
        if ((BitList.encodeTree a)[n]'(by simpa using hn)) then 1 else -1 := by
  rw [List.take_succ_eq_append_getElem (show n < (BitList.encodeTree a).length by simpa using hn),
    BitList.balance_append]
  simp [BitList.balance]

private theorem counter_get (i : ℤ) :
    (IntMemory.ofList [some true])[i] = if i = 0 then some true else none := by
  have h : IntMemory.ofList [some true] = (∅ : IntMemory (Option Bool)).set 0 (some true) :=
    (IntMemory.set_ofList_length [] (some true)).symm
  rw [h, IntMemory.getElem_set]
  simp only [IntMemory.getElem_empty, eq_comm]
  rfl

private theorem scanCfg_read (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (xs ys ws : List (Option Bool)) {n : ℕ}
    (hs : s ≠ d) (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hn : n < a.size) :
    (scanCfg u s d c copy a xs.length ys n).workSymbols s =
      some ((BitList.encodeTree a)[n]'(by simpa using hn)) := by
  simp only [TM.Cfg.workSymbols, scanCfg_workTapes, scanCfg_workPos,
    eq_self, ite_true, Function.update_of_ne hs, hx]
  change (IntMemory.ofList (xs ++ code a ++ ws))[(xs.length : ℤ) + n] = _
  rw [← Int.natCast_add, IntMemory.getElem_ofList_natCast, List.append_assoc,
    List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa using hn), List.getElem?_eq_getElem (by simpa using hn)]
  simp [code]

private theorem scanCfg_counter (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (p : ℕ) (ys : List (Option Bool)) {n : ℕ}
    (hc : c ≠ s) (hd : c ≠ d) (hx : u.workTapes c = IntMemory.ofList [some true])
    (hn : n ≤ a.size) :
    (scanCfg u s d c copy a p ys n).workSymbols c = some true ↔ n = a.size := by
  simp only [TM.Cfg.workSymbols, scanCfg_workTapes, scanCfg_workPos,
    hc, hd, ite_false, eq_self, ite_true, Function.update_of_ne hd, hx]
  rw [counter_get]
  by_cases h : 1 + BitList.balance ((BitList.encodeTree a).take n) = 0
  · simp only [h, ite_true, true_iff]
    exact (BitList.balance_take_encodeTree_eq_neg_one_iff a hn).mp (by omega)
  · simp only [h, ite_false, reduceCtorEq, false_iff]
    intro he
    have hb := (BitList.balance_take_encodeTree_eq_neg_one_iff a hn).mpr he
    omega

private theorem scanToken_apply (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (p : ℕ) (ys : List (Option Bool)) {n : ℕ}
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d) (hn : n < a.size) :
    apply
      (scanToken s d c copy ((BitList.encodeTree a)[n]'(by simpa using hn)))
        (scanCfg u s d c copy a p ys n) =
      scanCfg u s d c copy a p ys (n + 1) := by
  have hds := Ne.symm hs
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · exact TM.moveInputPos_zero _
  · funext i
    by_cases hi : i = d
    · subst i
      cases copy <;>
        simp [scanToken, hds, scanWord_succ _ _ _ hn,
          IntMemory.set_ofList_length]
    · by_cases hi' : i = s
      · subst i
        simp [scanToken, hi]
      · by_cases hi'' : i = c <;>
          simp [scanToken, hi, hi', hi'', hc, hd]
  · funext i
    by_cases hi : i = s
    · subst i
      simp [scanToken, SignType.cast]
      omega
    · by_cases hi' : i = d
      · subst i
        cases copy <;>
          simp [scanToken, hi, scanWord_succ _ _ _ hn,
            SignType.cast]
      · by_cases hi'' : i = c
        · subst i
          cases hb : ((BitList.encodeTree a)[n]'(by simpa using hn)) <;>
            simp [scanToken, hi, hi',
              balance_succ a hn, SignType.cast, hb, Int.add_assoc]
        · simp [scanToken, hi, hi', hi'', SignType.cast]
  · rfl

/-- At progress zero the scanner uses the caller's original configuration. -/
theorem scanCfg_zero (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (p : ℕ) (ys : List (Option Bool))
    (hy : u.workTapes d = IntMemory.ofList ys)
    (hs : u.workPos s = p) (hd : u.workPos d = ys.length) (hc : u.workPos c = 1) :
    scanCfg u s d c copy a p ys 0 = u := by
  apply TM.Cfg.ext
  · rfl
  · rfl
  · simp [scanWord, ← hy]
  · funext i
    by_cases hi : i = s
    · subst i; simp [hs]
    · by_cases hi' : i = d
      · subst i; simp [hi, scanWord, hd]
      · by_cases hi'' : i = c
        · subst i; simp [hi, hi', hc]
        · simp [hi, hi', hi'']
  · rfl

private def At (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (p : ℕ) (ys : List (Option Bool)) (V : κ → NonemptyInterval ℤ) (n : ℕ)
    (v : History (TM.Cfg κ (Option Bool) Unit zs) (TM.Action κ (Option Bool) Unit)) : Prop :=
  v.last = scanCfg u s d c copy a p ys n ∧ v.visited ≤ V

private theorem at_token (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (p : ℕ) (ys : List (Option Bool)) (V : κ → NonemptyInterval ℤ)
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hF : ∀ n, n ≤ a.size → ∀ i, (scanCfg u s d c copy a p ys n).workPos i ∈ V i)
    {n : ℕ} {v : History (TM.Cfg κ (Option Bool) Unit zs) (TM.Action κ (Option Bool) Unit)}
    (hn : n < a.size)
    (hv : At u s d c copy a p ys V n v) :
    At u s d c copy a p ys V (n + 1)
      (apply
        (scanToken s d c copy ((BitList.encodeTree a)[n]'(by simpa using hn))) v) := by
  have he : apply
      (scanToken s d c copy ((BitList.encodeTree a)[n]'(by simpa using hn))) v.last =
      scanCfg u s d c copy a p ys (n + 1) := by
    rw [hv.1, scanToken_apply u s d c copy a p ys hs hc hd hn]
  refine ⟨by simpa only [History.apply_last] using he, ?_⟩
  apply (v.apply_visited_le_iff _ V).mpr
  refine ⟨hv.2, ?_⟩
  simpa only [he] using hF (n + 1) (by omega)

set_option experimental.vcgen true in
private theorem body_progress (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (xs ys ws : List (Option Bool)) (V : κ → NonemptyInterval ℤ)
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hz : u.workTapes c = IntMemory.ofList [some true])
    (hF : ∀ n, n ≤ a.size → ∀ i,
      (scanCfg u s d c copy a xs.length ys n).workPos i ∈ V i)
    {n : ℕ} (hn : n < a.size) (q : ℕ) :
    Triple ((scanBody s d c copy).verify (TM.Program.semantics zs))
      (fun v b => At u s d c copy a xs.length ys V n v ∧ b = q + 3)
      (fun r v b => At u s d c copy a xs.length ys V (n + 1) v ∧
        (r = true ↔ n + 1 = a.size) ∧ b = q) () := by
  unfold scanBody
  vcgen
  case vc1 =>
    rename_i v b hv x v₁ b₁ h₁ y v₂ b₂ h₂ z v₃ b₃ h₃
    obtain ⟨hv,rfl⟩ := hv
    rcases h₁ with ⟨rfl, h₁, rfl⟩
    subst v₁
    rcases h₂ with ⟨rfl, h₂, rfl⟩
    subst v₂
    have he : decide (v.last.workSymbols s = some true) =
        ((BitList.encodeTree a)[n]'(by simpa using hn)) := by
      rw [hv.1,scanCfg_read u s d c copy a xs ys ws hs hx hn]
      cases ((BitList.encodeTree a)[n]'(by simpa using hn)) <;> rfl
    simp only [he] at h₃ ⊢
    have hv' := at_token u s d c copy a xs.length ys V hs hc hd hF
      (v := v.snoc TM.Program.idle) hn (by simpa [At] using hv)
    rcases h₃ with ⟨rfl,rfl,rfl⟩
    refine ⟨by simpa [At] using hv', ?_, by omega⟩
    simp only [decide_eq_true_eq, hv'.1]
    exact scanCfg_counter u s d c copy a xs.length ys hc hd hz (by omega)
  all_goals omega

/-- A common footprint contains the heads at every prefix boundary. -/
def ScanFootprint (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (p : ℕ) (ys : List (Option Bool)) (V : κ → NonemptyInterval ℤ) : Prop :=
  ∀ n, n ≤ a.size → ∀ i, (scanCfg u s d c copy a p ys n).workPos i ∈ V i

/-- The entire final configuration, footprint, and unused credits. -/
def ScanPost (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (p : ℕ) (ys : List (Option Bool)) (V : κ → NonemptyInterval ℤ) (q : ℕ)
    (v : History (TM.Cfg κ (Option Bool) Unit zs) (TM.Action κ (Option Bool) Unit))
    (b : ℕ) : Prop :=
  v.last = scanCfg u s d c copy a p ys a.size ∧ v.visited ≤ V ∧ b = q

/-- Scan one tree with four actual transitions per code bit, preserving an arbitrary suffix.

The result retains all unrelated tape data and all previously visited addresses. The caller
chooses a common footprint, which bounds the destination, source, and unary-counter heads.
Unused time credits are preserved for subsequent program blocks. -/
@[spec]
theorem spec_scan (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (xs ys ws : List (Option Bool)) (V : κ → NonemptyInterval ℤ) (q : ℕ)
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hy : u.workTapes d = IntMemory.ofList ys)
    (hz : u.workTapes c = IntMemory.ofList [some true])
    (hp : u.workPos s = xs.length) (hi : u.workPos d = ys.length) (hj : u.workPos c = 1)
    (hF : ScanFootprint u s d c copy a xs.length ys V) :
    Triple ((scan s d c copy).verify (TM.Program.semantics zs))
      (fun v b => v.last = u ∧ v.visited ≤ V ∧ b = 4 * a.size + q)
      (fun _ v b => ScanPost u s d c copy a xs.length ys V q v b) () := by
  have hn : a.size - 1 + 1 = a.size := by have := Tree.size_pos a; omega
  have hl := Program.spec_repeatUntilWith_count TM.Program.idle
    (scanBody s d c copy) (TM.Program.semantics zs)
    (At u s d c copy a xs.length ys V)
    (At u s d c copy a xs.length ys V a.size) (a.size - 1) 3 3 q
    (fun _ _ v hv ↦ by simpa [At] using hv)
    (fun r hr z ↦ by
      constructor
      rintro v b hv
      apply (Triple.entails_wp_of_post
        (body_progress u s d c copy a xs ys ws V hs hc hd hx hz hF
          (show r < a.size by omega) z) ?_) v b ⟨hv.1, by omega⟩
      rintro b v t ⟨hv, hb, ht⟩
      exact ⟨Bool.eq_false_iff.mpr (fun h ↦ by have := hb.mp h; omega), hv, ht⟩)
    (fun z ↦ by
      constructor
      rintro v b hv
      apply (Triple.entails_wp_of_post
        (body_progress u s d c copy a xs ys ws V hs hc hd hx hz hF
          (show a.size - 1 < a.size by omega) z) ?_) v b ⟨hv.1, by omega⟩
      rintro b v t ⟨hv, hb, ht⟩
      exact ⟨hb.mpr hn, hn ▸ hv, ht⟩)
  constructor
  rintro v b ⟨hv, hR, hb⟩
  apply (Triple.entails_wp_of_post hl (fun _ w z h ↦
    ⟨h.1.1, h.1.2, h.2⟩)) v b
  refine ⟨⟨?_, hR⟩, ?_⟩
  · simpa only [scanCfg_zero u s d c copy a xs.length ys hy hp hi hj] using hv
  · omega

/-- A scanner's final footprint bounds all work cells it has visited. -/
theorem ScanPost.space_le [Fintype κ] {u : TM.Cfg κ (Option Bool) Unit zs} {s d c : κ}
    {copy : Bool} {a : Tree} {p : ℕ} {ys : List (Option Bool)}
    {V : κ → NonemptyInterval ℤ} {q b : ℕ}
    {v : History (TM.Cfg κ (Option Bool) Unit zs) (TM.Action κ (Option Bool) Unit)}
    (h : ScanPost u s d c copy a p ys V q v b) :
    v.space ≤ ∑ i, ((V i).snd + 1 - (V i).fst).toNat :=
  v.space_le_of_visited_le V h.2.1

end Complexity.TreeMachine.Program
