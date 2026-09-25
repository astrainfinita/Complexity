/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Write
public import Complexity.Models.TreeMachine.Program.Scan.Configuration
public import Complexity.Models.TuringMachine.Program.Word.Configuration

/-! # Child projection by composing prefix scanning, copying, and rewinding -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Program

open TM TM.Program.Word Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Pass the pair tag and initialize the unary pending-subtree counter. -/
def projectAdvance (j k : κ) : TM.Action κ (Option Bool) Unit :=
  { TM.Program.idle (κ := κ) with
    work := fun l ↦ (none, if l = j ∨ l = k then 1 else 0) }

/-- Branch on the root already read, then restore the participating heads. -/
def projectTail (i j k : κ) (right : Bool) (a : Option Bool) : TM.Program κ (Option Bool) Unit := do
  if a = some false then
    put i (some false)
  else
    TM.Program.act (projectAdvance j k)
    scan j i k (!right)
    if right then copy i j else pure ()
    rewind j
  rewind i

/-- Project one child, preserving the encoded source and restoring every participating head. -/
def project (i j k : κ) (right : Bool) : TM.Program κ (Option Bool) Unit := do
  let a ← TM.Program.read j
  projectTail i j k right a

/-- Projection changes only the destination tree. -/
@[simps -fullyApplied]
def projected (c : TM.Cfg κ (Option Bool) Unit xs) (i : κ) (a : Tree) (right : Bool) :
    TM.Cfg κ (Option Bool) Unit xs :=
  { c with
    workTapes := Function.update c.workTapes i
      (tape (BitList.encodeTree (if right then a.right else a.left))) }

/-- Exact local-action count for child projection. -/
def projectTime : Tree → Bool → ℕ
  | .nil, _ => 9
  | .node _ a _, false => 10 * Tree.size a + 13
  | .node _ a b, true => 7 * Tree.size a + 9 * Tree.size b + 15

/-- A uniform linear bound convenient for whole-machine simulation. -/
theorem projectTime_le (a : Tree) (right : Bool) : projectTime a right ≤ 30 * (a.size + 1) := by
  cases a <;> cases right <;> simp only [projectTime, Tree.size] <;> omega

@[simps -fullyApplied]
private def scanned (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (a : Tree)
    (right : Bool) : TM.Cfg κ (Option Bool) Unit xs :=
  { c with
    workTapes := Function.update c.workTapes i (tape (if right then [] else BitList.encodeTree a))
    workPos := fun q ↦ if q = j then 1 + a.size
      else if q = i then if right then 0 else a.size else c.workPos q }

private theorem scan_terminal (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a : Tree) (right : Bool) (hk : c.workPos k = 0) :
    scanCfg (apply (projectAdvance j k) c)
      j i k (!right) a 1 [] a.size =
      scanned c i j a right := by
  have htake : (code a).take a.size = code a := by simp
  have hb : BitList.balance ((BitList.encodeTree a).take a.size) = -1 := by
    rw [← BitList.length_encodeTree a, List.take_length, BitList.balance_encodeTree]
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · funext q
    cases right <;>
      simp only [scanCfg_workTapes, scanned_workTapes, scanWord, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, htake] <;> rfl
  · funext q
    by_cases hqj : q = j
    · subst q
      simp
    · by_cases hqi : q = i
      · subst q
        cases right <;> simp [hqj, scanWord, htake]
      · by_cases hqk : q = k
        · subst q
          simp [hqj, hqi, hb, hk]
        · simp [hqj, hqi, hqk, projectAdvance]
  · rfl

omit [DecidableEq κ] in
private theorem read_tree (c : TM.Cfg κ (Option Bool) Unit xs) (j : κ) (a : Tree)
    (ht : c.workTapes j = tape (BitList.encodeTree a)) (hp : c.workPos j = 0) :
    c.workSymbols j = some a.root := by
  simp only [TM.Cfg.workSymbols, ht, hp]
  change (tape (BitList.encodeTree a))[((0 : ℕ) : ℤ)] = _
  rw [tape_get]
  cases a <;> rfl

private theorem left_finished (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (a b : Tree) (hi : c.workPos i = 0) (hj : c.workPos j = 0) :
    let d := scanned c i j a false
    let e := { d with workPos := Function.update d.workPos j 0 }
    { e with workPos := Function.update e.workPos i 0 } = projected c i (Tree.pair a b) false := by
  dsimp
  apply TM.Cfg.ext <;> try rfl
  funext q
  by_cases hqi : q = i
  · subst q
    simpa using hi.symm
  · by_cases hqj : q = j
    · subst q
      simpa [hqi] using hj.symm
    · simp [hqi, hqj]

private theorem right_finished (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (a b : Tree) (hi : c.workPos i = 0) (hj : c.workPos j = 0) :
    let d := copied (scanned c i j a true) i j [] (BitList.encodeTree b)
    let e := { d with workPos := Function.update d.workPos j 0 }
    { e with workPos := Function.update e.workPos i 0 } = projected c i (Tree.pair a b) true := by
  dsimp
  apply TM.Cfg.ext <;> try rfl
  · simp
  · funext q
    by_cases hqi : q = i
    · subst q
      simpa using hi.symm
    · by_cases hqj : q = j
      · subst q
        simpa [hqi] using hj.symm
      · simp [hqi, hqj]

private theorem nil_finished (c : TM.Cfg κ (Option Bool) Unit xs) (i : κ)
    (right : Bool) (hw : c.workTapes i = tape []) (hi : c.workPos i = 0) :
    let d := apply (putAction i (some false)) c
    { d with workPos := Function.update d.workPos i 0 } = projected c i Tree.nil right := by
  dsimp
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · funext q
    by_cases h : q = i
    · subst q
      have he := tape_append [] false
      cases right <;>
        simpa [putAction, hw, hi, BitList.encodeTree] using he
    · cases right <;> simp [putAction, h]
  · funext q
    by_cases h : q = i
    · subst q
      simpa using hi.symm
    · simp [putAction, h]
  · rfl

private theorem spec_pair_scan (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a b : Tree) (right : Bool) (q : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hw : c.workTapes i = tape []) (ht : c.workTapes j = tape (BitList.encodeTree (Tree.pair a b)))
    (hc : c.workTapes k = IntMemory.ofList [some true])
    (hi : c.workPos i = 0) (hj : c.workPos j = 0)
    (hk : c.workPos k = 0) :
    Triple ((scan j i k (!right)).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = apply (projectAdvance j k) c ∧
        z = 4 * a.size + q)
      (fun _ d z ↦ d = scanned c i j a right ∧ z = q) () := by
  have h := spec_scan_cfg
    (apply (projectAdvance j k) c) j i k (!right) a
    [some true] [] (code b) q hij.symm hjk.symm hik.symm
    (by simpa [projectAdvance, tape, BitList.encodeTree, code,
      List.map_append] using ht)
    (by simpa [projectAdvance, tape] using hw)
    (by simpa [projectAdvance, tape] using hc)
    (by simp [projectAdvance, hj])
    (by simp [projectAdvance, hij, hik, hi])
    (by simp [projectAdvance, hk])
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
    scan_terminal c i j k a right hk] using h

private theorem spec_tail_nil (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (right : Bool) (q : ℕ) (hw : c.workTapes i = tape []) (hi : c.workPos i = 0) :
    Triple ((projectTail i j k right (some false)).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = c ∧ z = 8 + q)
      (fun _ d z ↦ d = projected c i Tree.nil right ∧ z = q) () := by
  let d := apply (putAction i (some false)) c
  have h := spec_rewind_cfg d i [false] 1 q
    (by simpa [d, putAction, hw, hi] using tape_append [] false)
    (by simp [d, putAction, hi]) (by simp)
  unfold projectTail put
  simp only [↓reduceIte]
  vcgen [h]
  all_goals try { rename_i h; exact ⟨h.1.trans (nil_finished c i right hw hi), h.2⟩ }
  all_goals simp_all [d]

private theorem spec_tail_left (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a b : Tree) (q : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hw : c.workTapes i = tape []) (ht : c.workTapes j = tape (BitList.encodeTree (Tree.pair a b)))
    (hc : c.workTapes k = IntMemory.ofList [some true])
    (hi : c.workPos i = 0) (hj : c.workPos j = 0)
    (hk : c.workPos k = 0) :
    Triple ((projectTail i j k false (some true)).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = c ∧ z = 10 * a.size + 12 + q)
      (fun _ d z ↦ d = projected c i (Tree.pair a b) false ∧ z = q) () := by
  let d := scanned c i j a false
  let e := { d with workPos := Function.update d.workPos j 0 }
  have h₁ := spec_pair_scan c i j k a b false
    ((3 * (a.size + 1) + 4) + (3 * a.size + 4) + q)
    hij hik hjk hw ht hc hi hj hk
  have h₂ := spec_rewind_cfg d j (BitList.encodeTree (Tree.pair a b)) (a.size + 1)
    (3 * a.size + 4 + q)
    (by simp [d, hij.symm, ht])
    (by simp [d]; omega) (by simp)
  have h₃ := spec_rewind_cfg e i (BitList.encodeTree a) a.size q
    (by simp [e, d])
    (by simp [e, d, hij]) (by simp)
  unfold projectTail
  simp only [Option.some.injEq, Bool.true_eq_false, ↓reduceIte, Bool.false_eq_true]
  vcgen [h₁, h₂, h₃]
  all_goals try { rename_i h; exact ⟨h.1.trans (left_finished c i j a b hi hj), h.2⟩ }
  all_goals simp_all [d, e]
  all_goals omega

private theorem spec_tail_right (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a b : Tree) (q : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hw : c.workTapes i = tape []) (ht : c.workTapes j = tape (BitList.encodeTree (Tree.pair a b)))
    (hc : c.workTapes k = IntMemory.ofList [some true])
    (hi : c.workPos i = 0) (hj : c.workPos j = 0)
    (hk : c.workPos k = 0) :
    Triple ((projectTail i j k true (some true)).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = c ∧ z = 7 * a.size + 9 * b.size + 14 + q)
      (fun _ d z ↦ d = projected c i (Tree.pair a b) true ∧ z = q) () := by
  let d := scanned c i j a true
  let e := copied d i j [] (BitList.encodeTree b)
  let f := { e with workPos := Function.update e.workPos j 0 }
  have h₁ := spec_pair_scan c i j k a b true
    ((3 * b.size + 2) + (3 * (a.size + b.size + 1) + 4) +
      (3 * b.size + 4) + q) hij hik hjk hw ht hc hi hj hk
  have h₂ := spec_copy_cfg d i j [] (true :: BitList.encodeTree a) (BitList.encodeTree b)
    ((3 * (a.size + b.size + 1) + 4) + (3 * b.size + 4) + q) hij
    (by simpa [d, hij.symm, BitList.encodeTree] using ht)
    (by simp [d]; omega)
    (by simp [d])
    (by simp [d, hij])
  have h₃ := spec_rewind_cfg e j (BitList.encodeTree (Tree.pair a b)) (a.size + b.size + 1)
    (3 * b.size + 4 + q)
    (by simp [e, d, hij.symm, ht])
    (by simp [e, d, hij.symm]; omega) (by simp)
  have h₄ := spec_rewind_cfg f i (BitList.encodeTree b) b.size q
    (by simp [f, e])
    (by simp [f, e, d, hij]) (by simp)
  unfold projectTail
  simp only [Option.some.injEq, Bool.true_eq_false, ↓reduceIte]
  vcgen [h₁, h₂, h₃, h₄]
  all_goals try { rename_i h; exact ⟨h.1.trans (right_finished c i j a b hi hj), h.2⟩ }
  all_goals simp_all [d, e, f]
  all_goals omega

private theorem spec_tail (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a : Tree) (right : Bool) (q : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hw : c.workTapes i = tape []) (ht : c.workTapes j = tape (BitList.encodeTree a))
    (hc : c.workTapes k = IntMemory.ofList [some true])
    (hi : c.workPos i = 0) (hj : c.workPos j = 0)
    (hk : c.workPos k = 0) :
    Triple ((projectTail i j k right (some a.root)).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = c ∧ z = projectTime a right - 1 + q)
      (fun _ d z ↦ d = projected c i a right ∧ z = q) () := by
  cases a with
  | nil => simpa only [projectTime, Tree.root, Nat.reduceSub] using
      spec_tail_nil c i j k right q hw hi
  | node u a b =>
    cases u
    cases right
    · have he : projectTime (Tree.pair a b) false - 1 = 10 * Tree.size a + 12 := by
        simp only [projectTime]; omega
      simpa only [Tree.root, he] using
        spec_tail_left c i j k a b q hij hik hjk hw ht hc hi hj hk
    · have he : projectTime (Tree.pair a b) true - 1 =
          7 * Tree.size a + 9 * Tree.size b + 14 := by
        simp only [projectTime]; omega
      simpa only [Tree.root, he] using
        spec_tail_right c i j k a b q hij hik hjk hw ht hc hi hj hk

/-- Child projection preserves the source, counter, all heads, and all input/output fields.
The exact action count leaves an arbitrary amount of continuation credit available. -/
@[spec]
theorem spec_project_cfg (c : TM.Cfg κ (Option Bool) Unit xs) (i j k : κ)
    (a : Tree) (right : Bool) (q : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hw : c.workTapes i = tape []) (ht : c.workTapes j = tape (BitList.encodeTree a))
    (hc : c.workTapes k = IntMemory.ofList [some true])
    (hi : c.workPos i = 0) (hj : c.workPos j = 0)
    (hk : c.workPos k = 0) :
    Triple ((project i j k right).verify (TM.Program.cfgSemantics xs))
      (fun d z ↦ d = c ∧ z = projectTime a right + q)
      (fun _ d z ↦ d = projected c i a right ∧ z = q) () := by
  have h (x : Option Bool) :
      Triple ((projectTail i j k right x).verify (TM.Program.cfgSemantics xs))
        (fun d z ↦ x = some a.root ∧ d = c ∧ z = projectTime a right - 1 + q)
        (fun _ d z ↦ d = projected c i a right ∧ z = q) () := by
    constructor
    rintro d z ⟨rfl, hd, hz⟩
    exact (spec_tail c i j k a right q hij hik hjk hw ht hc hi hj hk).le_wp d z ⟨hd, hz⟩
  have hr := read_tree c j a ht hj
  have hp : 0 < projectTime a right := by cases a <;> cases right <;> simp [projectTime]
  unfold project
  vcgen [h]
  all_goals simp_all
  all_goals omega

end Complexity.TreeMachine.Program
