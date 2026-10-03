/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Traverse
public import Complexity.Models.TreeMachine.Encoding
public import Complexity.Models.TuringMachine.Program.Specification.Configuration
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

set_option experimental.vcgen true in
private theorem body_progress (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ)
    (copy : Bool) (a : Tree) (xs ys ws : List (Option Bool))
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hz : u.workTapes c = IntMemory.ofList [some true])
    {n : ℕ} (hn : n < a.size) (q : ℕ) :
    Triple ((scanBody s d c copy).verify (TM.Program.cfgSemantics zs))
      (fun v b => v = scanCfg u s d c copy a xs.length ys n ∧ b = q + 3)
      (fun r v b => v = scanCfg u s d c copy a xs.length ys (n + 1) ∧
        (r = true ↔ n + 1 = a.size) ∧ b = q) () := by
  have he := scanCfg_read u s d c copy a xs ys ws hs hx hn
  have ha := scanToken_apply u s d c copy a xs.length ys hs hc hd hn
  have hz' := scanCfg_counter u s d c copy a xs.length ys hc hd hz
    (show n + 1 ≤ a.size by omega)
  unfold scanBody
  vcgen
  all_goals simp_all

/-- Scan one tree prefix, retaining the complete final tapes and unused time credits.

The source prefix, arbitrary suffix, all unrelated storage, and exact unused credits
are preserved according to `scanCfg`.
-/
@[spec]
theorem spec_scan_cfg (u : TM.Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (xs ys ws : List (Option Bool)) (q : ℕ)
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hy : u.workTapes d = IntMemory.ofList ys)
    (hz : u.workTapes c = IntMemory.ofList [some true])
    (hp : u.workPos s = xs.length) (hi : u.workPos d = ys.length) (hj : u.workPos c = 1) :
    Triple ((scan s d c copy).verify (TM.Program.cfgSemantics zs))
      (fun v b ↦ v = u ∧ b = 4 * a.size + q)
      (fun _ v b ↦ v = scanCfg u s d c copy a xs.length ys a.size ∧ b = q) () := by
  have hn : a.size - 1 + 1 = a.size := by have := Tree.size_pos a; omega
  have hl := Program.spec_repeatUntilWith_count TM.Program.idle
    (scanBody s d c copy) (TM.Program.cfgSemantics zs)
    (fun n v ↦ v = scanCfg u s d c copy a xs.length ys n)
    (fun v ↦ v = scanCfg u s d c copy a xs.length ys a.size) (a.size - 1) 3 3 q
    (fun _ _ v hv ↦ by simpa only [TM.Program.cfgSemantics_act, TM.Program.idle_apply] using hv)
    (fun r hr z ↦ by
      constructor
      rintro v b hv
      apply (Triple.entails_wp_of_post
        (body_progress u s d c copy a xs ys ws hs hc hd hx hz
          (show r < a.size by omega) z) ?_) v b ⟨hv.1, by omega⟩
      rintro b v t ⟨hv, hb, ht⟩
      exact ⟨Bool.eq_false_iff.mpr (fun h ↦ by have := hb.mp h; omega), hv, ht⟩)
    (fun z ↦ by
      constructor
      rintro v b hv
      apply (Triple.entails_wp_of_post
        (body_progress u s d c copy a xs ys ws hs hc hd hx hz
          (show a.size - 1 < a.size by omega) z) ?_) v b ⟨hv.1, by omega⟩
      rintro b v t ⟨hv, hb, ht⟩
      exact ⟨hb.mpr hn, hn ▸ hv, ht⟩)
  simpa only [scan, TM.Program.repeatUntil, hn,
    scanCfg_zero u s d c copy a xs.length ys hy hp hi hj,
    show (3 + 1) * (a.size - 1) + 3 + 1 + q = 4 * a.size + q by omega] using hl

end Complexity.TreeMachine.Program
