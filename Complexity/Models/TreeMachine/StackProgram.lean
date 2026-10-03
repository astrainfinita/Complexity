/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Program.Word
public import Complexity.Data.Tree.Encoding

/-! # Tree operations on ordinary binary stacks -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.StackMachine.Program.Tree

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array Bool}

/-- The pending forest is ghost data; the actual counter stores one bit per pending tree. -/
def forestCode (fs : List Complexity.Tree) : List Bool := fs.flatMap BitList.encodeTree

/-- Consume one token, save it, and update the pending-subtree counter. -/
def scanAction (source saved counter : κ) (b : Bool) : Action κ Bool Unit :=
  { idle (κ := κ) with work := fun i ↦ if i = source then .pop else if i = saved then .push b
    else if i = counter then if b then .push true else .pop else .nop }

/-- Process one token and stop when the counter becomes empty. -/
def scanBody (source saved counter : κ) : StackMachine.Program κ Bool Bool := do
  let b ← read source
  act (scanAction source saved counter (b.getD false))
  let n ← read counter
  pure n.isNone

/-- Consume one encoded tree, saving its reversed code. The counter starts with one bit. -/
def scan (source saved counter : κ) : StackMachine.Program κ Bool Unit :=
  repeatUntil (scanBody source saved counter)

/-- Complete configuration with a pending forest and the reversed processed prefix. -/
@[simps -fullyApplied]
def scanning (c : Cfg κ Bool Unit xs) (source saved counter : κ)
    (fs : List Complexity.Tree) (p suffix : List Bool) : Cfg κ Bool Unit xs :=
  { c with «stacks» := fun i ↦ if i = source then forestCode fs ++ suffix
    else if i = saved then p.reverse ++ c.stacks i
    else if i = counter then List.replicate fs.length true else c.stacks i }

variable (source saved counter : κ) (hs : source ≠ saved) (hc : source ≠ counter)
  (hsc : saved ≠ counter)

include hc hsc in
/-- The scan preserves every unrelated stack and the external streams. -/
@[spec] theorem spec_scan (c : Cfg κ Bool Unit xs) (a : Complexity.Tree)
    (suffix : List Bool) (q : ℕ) :
    Triple ((scan source saved counter).verify (semantics xs))
      (fun s b ↦ s = scanning c source saved counter [a] [] suffix ∧ b = 4 * a.size + q)
      (fun _ s b ↦ s = scanning c source saved counter [] (BitList.encodeTree a) suffix ∧
        b = q) () := by
  let I : Cfg κ Bool Unit xs → ℕ → Prop := fun s b ↦ ∃ fs p, fs ≠ [] ∧
    s = scanning c source saved counter fs p suffix ∧
    p ++ forestCode fs = BitList.encodeTree a ∧ b = 4 * (forestCode fs).length + q
  have h : Triple ((scan source saved counter).verify (semantics xs)) I
      (fun _ s b ↦ s = scanning c source saved counter [] (BitList.encodeTree a) suffix ∧
        b = q) () := by
    apply Program.spec_repeatUntilWith_nop idle (scanBody source saved counter)
      (semantics xs) I _ ()
    · exact idle_apply
    · rintro s b ⟨fs, p, hf, rfl, hp, hb⟩
      cases fs with
      | nil => contradiction
      | cons t fs =>
        have ht := Complexity.Tree.size_pos t
        simp only [forestCode, List.flatMap_cons, List.length_append,
          BitList.length_encodeTree] at hb
        omega
    · constructor
      rintro s b ⟨fs, p, hf, rfl, hp, hb⟩
      cases fs with
      | nil => contradiction
      | cons t fs =>
        obtain ⟨bit, fs', hlen, hn⟩ : ∃ bit fs',
            forestCode (t :: fs) = bit :: forestCode fs' ∧
            apply (scanAction source saved counter bit)
              (scanning c source saved counter (t :: fs) p suffix) =
              scanning c source saved counter fs' (p ++ [bit]) suffix := by
          cases t
          case' nil => refine ⟨false, fs, rfl, ?_⟩
          case' node u l r =>
            cases u
            refine ⟨true, l :: r :: fs, ?_, ?_⟩
            · simp [forestCode, BitList.encodeTree, List.append_assoc]
          all_goals
            ext i <;> simp [scanAction, idle, StackMachine.Op.apply, forestCode,
              BitList.encodeTree, List.reverse_append, List.replicate_succ, List.append_assoc]
            split_ifs <;> simp_all
        have he : (List.replicate fs'.length true).head?.isNone = fs'.isEmpty := by
          cases fs' <;> rfl
        have hbody : Triple ((scanBody source saved counter).verify (semantics xs))
            (fun s z ↦ s = scanning c source saved counter (t :: fs) p suffix ∧
              z = 3 + (b - 3))
            (fun r s z ↦ r = fs'.isEmpty ∧
              s = scanning c source saved counter fs' (p ++ [bit]) suffix ∧
              z = b - 3) () := by
          unfold scanBody
          vcgen
          all_goals simp_all [Ne.symm hc, Ne.symm hsc]
        rw [hlen] at hp hb
        simp only [List.length_cons] at hb
        apply (Triple.entails_wp_of_post hbody ?_) _ b ⟨rfl, by omega⟩
        rintro r s z ⟨rfl, rfl, rfl⟩
        cases fs' with
        | nil => simpa [forestCode, ← hp, List.append_assoc] using
            (show b - 3 = q by simp [forestCode] at hb; omega)
        | cons t fs =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
          refine ⟨t :: fs, p ++ [bit], by simp, rfl, ?_, ?_⟩
          · simpa [List.append_assoc] using hp
          · omega
  constructor
  rintro s b ⟨rfl, rfl⟩
  apply h.le_wp
  exact ⟨[a], [], by simp, rfl, by simp [forestCode], by simp [forestCode]⟩

/-- Initialize the unary counter and consume the first tree. -/
def takeTree (source saved counter : κ) : StackMachine.Program κ Bool Unit := do
  push counter true
  scan source saved counter

include hs hc hsc in
/-- A tree may be followed by any suffix; unrelated storage is preserved. -/
@[spec] theorem spec_takeTree (c : Cfg κ Bool Unit xs) (a : Complexity.Tree)
    (suffix : List Bool) (q : ℕ) (ha : c.stacks source = BitList.encodeTree a ++ suffix)
    (hn : c.stacks counter = []) :
    Triple ((takeTree source saved counter).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 4 * a.size + 1 + q)
      (fun _ s b ↦ s = (c.setStack source suffix).setStack saved
        ((BitList.encodeTree a).reverse ++ c.stacks saved) ∧ b = q) () := by
  have hi : c.setStack counter [true] = scanning c source saved counter [a] [] suffix := by
    ext i <;> simp [forestCode, Function.update_apply]
    split_ifs <;> simp_all
  have he : scanning c source saved counter [] (BitList.encodeTree a) suffix =
      (c.setStack source suffix).setStack saved
        ((BitList.encodeTree a).reverse ++ c.stacks saved) := by
    ext i <;> simp [forestCode, Function.update_apply]
    split_ifs <;> simp_all
  have ht := spec_scan source saved counter hc hsc c a suffix q
  unfold takeTree
  vcgen [ht]
  all_goals simp_all

/-- Copy the first tree and restore the source, using two empty scratch stacks. -/
def copyTree (source target saved counter : κ) : StackMachine.Program κ Bool Unit := do
  takeTree source saved counter
  Word.drain saved (fun i ↦ i == source || i == target)

include hs hc hsc in
@[spec] theorem spec_copyTree (c : Cfg κ Bool Unit xs) (target : κ) (a : Complexity.Tree)
    (suffix : List Bool) (q : ℕ) (hst : source ≠ target) (hts : target ≠ saved)
    (ha : c.stacks source = BitList.encodeTree a ++ suffix)
    (hn : c.stacks counter = []) (hp : c.stacks saved = []) :
    Triple ((copyTree source target saved counter).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 7 * a.size + 3 + q)
      (fun _ s b ↦ s = c.setStack target (BitList.encodeTree a ++ c.stacks target) ∧ b = q) () := by
  let d := (c.setStack source suffix).setStack saved (BitList.encodeTree a).reverse
  have he : Word.drained d saved (fun i ↦ i == source || i == target) (d.stacks saved) [] =
      c.setStack target (BitList.encodeTree a ++ c.stacks target) := by
    ext i <;> simp [d, Function.update_apply]
    split_ifs <;> simp_all
  have h₁ := spec_takeTree source saved counter hs hc hsc c a suffix (3 * a.size + 2 + q) ha hn
  have h₂ := Word.spec_drain d saved (fun i ↦ i == source || i == target) q
  unfold copyTree
  vcgen [h₁, h₂]
  all_goals simp_all [d] <;> omega

/-- Copy the right word first, then the left word, and prepend the node token. -/
def pair (left right target temp : κ) : StackMachine.Program κ Bool Unit := do
  Word.copy right target temp
  Word.copy left target temp
  push target true

/-- Pairing accepts arbitrary binary words and preserves both sources. -/
@[spec] theorem spec_pair (c : Cfg κ Bool Unit xs) (left right target temp : κ)
    (u v : List Bool) (q : ℕ) (hlt : left ≠ target) (hlp : left ≠ temp)
    (hrt : right ≠ target) (hrp : right ≠ temp) (htp : target ≠ temp)
    (ha : c.stacks left = u) (hb : c.stacks right = v)
    (hp : c.stacks temp = []) :
    Triple ((pair left right target temp).verify (semantics xs))
      (fun s n ↦ s = c ∧ n = 6 * (u.length + v.length) + 9 + q)
      (fun _ s n ↦ s = c.setStack target ((true :: (u ++ v)) ++
        c.stacks target) ∧ n = q) () := by
  have h₁ := Word.spec_copy c right target temp (6 * u.length + 5 + q) hrt hrp htp hp
  have h₂ := Word.spec_copy (c.setStack target (v ++ c.stacks target))
    left target temp (q + 1) hlt hlp htp (by simp [Ne.symm htp, hp])
  unfold pair
  vcgen [h₁, h₂]
  all_goals simp_all [List.append_assoc] <;> omega

/-- Project one child while preserving the source and every other register. -/
def project (source target saved temp counter : κ) (right : Bool) :
    StackMachine.Program κ Bool Unit := do
  let b ← read source
  if b.getD false then
    pop source
    if right then
      takeTree source saved counter
      copyTree source target temp counter
      Word.drain saved (fun i ↦ i == source)
      push source true
    else
      copyTree source target saved counter
      push source true
  else push target false

/-- Exact transition count, including restoration of the source and scratch stacks. -/
def projectTime (a : Complexity.Tree) (right : Bool) : ℕ :=
  match a with
  | .nil => 2
  | .node _ l r => if right then 7 * (Complexity.Tree.size l + Complexity.Tree.size r) + 9
    else 7 * Complexity.Tree.size l + 6

theorem projectTime_le (a : Complexity.Tree) (right : Bool) :
    projectTime a right ≤ 7 * a.size + 9 := by
  cases a <;> simp only [projectTime, Complexity.Tree.size]
  · omega
  · split_ifs <;> omega

@[spec] theorem spec_project (c : Cfg κ Bool Unit xs) (source target saved temp counter : κ)
    (a : Complexity.Tree) (suffix : List Bool) (right : Bool) (q : ℕ)
    (hi : [source, target, saved, temp, counter].Nodup)
    (ha : c.stacks source = BitList.encodeTree a ++ suffix)
    (hsaved : c.stacks saved = []) (htemp : c.stacks temp = [])
    (hcounter : c.stacks counter = []) :
    Triple ((project source target saved temp counter right).verify (semantics xs))
      (fun s n ↦ s = c ∧ n = projectTime a right + q)
      (fun _ s n ↦ s = c.setStack target
        (BitList.encodeTree (if right then a.right else a.left) ++ c.stacks target) ∧
        n = q) () := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hi
  obtain ⟨⟨hst, hss, hsp, hsc⟩, ⟨hts, htp, htc⟩, ⟨hsp', hsc'⟩, hpc⟩ := hi
  cases a with
  | nil =>
    unfold project
    vcgen
    all_goals simp_all [BitList.encodeTree, projectTime, BinaryTree.left, BinaryTree.right]
  | node u l r =>
    cases u
    simp only [BitList.encodeTree, List.cons_append, List.append_assoc] at ha
    let d := c.setStack source (BitList.encodeTree l ++ BitList.encodeTree r ++ suffix)
    have hd : d.stacks source = BitList.encodeTree l ++ (BitList.encodeTree r ++ suffix) := by
      simp [d, List.append_assoc]
    have hn : d.stacks counter = [] := by simp [d, Ne.symm hsc, hcounter]
    have hs : d.stacks saved = [] := by simp [d, Ne.symm hss, hsaved]
    have hp : d.stacks temp = [] := by simp [d, Ne.symm hsp, htemp]
    have hpop : c.setStack source (c.stacks source).tail = d := by
      simp [ha, d]
    have restore (w : List Bool) : (d.setStack target w).setStack source
        (true :: (d.setStack target w).stacks source) = c.setStack target w := by
      rw [Cfg.setStack_comm _ (Ne.symm hst)]
      simp [d, hst, ← ha]
    cases right with
    | false =>
      have ht := spec_copyTree source saved counter hss hsc hsc' d target l
        (BitList.encodeTree r ++ suffix) (q + 1) hst hts hd hn hs
      unfold project
      vcgen [ht]
      all_goals simp_all [projectTime, BinaryTree.left, d, Ne.symm hst]
      all_goals omega
    | true =>
      let e := (d.setStack source (BitList.encodeTree r ++ suffix)).setStack saved
        (BitList.encodeTree l).reverse
      let f := e.setStack target (BitList.encodeTree r ++ e.stacks target)
      have ht₁ := spec_takeTree source saved counter hss hsc hsc' d l
        (BitList.encodeTree r ++ suffix) (7 * Complexity.Tree.size r +
          3 * Complexity.Tree.size l + 6 + q) hd hn
      have ht₂ := spec_copyTree source temp counter hsp hsc hpc e target r suffix
        (3 * Complexity.Tree.size l + 3 + q) hst htp
        (by simp [e, hss]) (by simp [e, Ne.symm hsc', Ne.symm hsc, hn])
        (by simp [e, Ne.symm hsp', Ne.symm hsp, hp])
      have ht₃ := Word.spec_drain f saved (fun i ↦ i == source) (q + 1)
      have he : Word.drained f saved (fun i ↦ i == source) (f.stacks saved) [] =
          d.setStack target (BitList.encodeTree r ++ c.stacks target) := by
        ext i <;> simp [f, e, d, Function.update_apply]
        split_ifs <;> simp_all
      unfold project
      vcgen [ht₁, ht₂, ht₃]
      all_goals simp_all [projectTime, BinaryTree.right, f, e, d,
        Ne.symm hss, Ne.symm hsc, Ne.symm hsp, Ne.symm hst,
        Ne.symm hts]
      all_goals omega

end Complexity.StackMachine.Program.Tree
