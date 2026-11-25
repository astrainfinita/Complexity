/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeFunctions.Decompile

/-! # Recognizing codes in polynomial time

`dom_decode_nat_mem_p`, `dom_decode_list_mem_p`: the codes of natural numbers, and the codes of
lists over a type whose codes are recognized in polynomial time, are recognized in polynomial time.
These are the recognizers of codes that `p_guard` takes.

A tree is the code of a list when every tree of its spine is the code of an element
(`exists_encode_list_eq_iff`); the recognizer of a list checks its spine by a fold, with the
recognizer of the elements decompiled into a tree program (`exists_hasProgramIn_of_mem_fp`). The
code of a natural number is that of its binary digits: a list of Booleans whose last element, if
any, is `true`. The checks are written as folds, since a check by `List.all` of the trees of a spine
does not get its peak bounded by `dominated` (translation plan W92); this is the current state, not
a decision.
-/

@[expose] public section

namespace Complexity

open TreeProgram TreeProgram.Source

/-- A fold of `&&` from `true` checks every element. -/
private theorem foldl_and_eq_true {α : Type*} (p : α → Bool) (l : List α) :
    l.foldl (fun b a => b && p a) true = true ↔ ∀ a ∈ l, p a = true := by
  suffices ∀ c, l.foldl (fun b a => b && p a) c = (c && l.all p) by simp [this]
  induction l with
  | nil => simp
  | cons a l ih => intro c; simp [ih, Bool.and_assoc]

/-- A fold keeping the latest element gives the last element. -/
private theorem foldl_last_eq_getLastD (xs : List Bool) (c : Bool) :
    xs.foldl (fun _ b => b) c = xs.getLast?.getD c := by
  induction xs generalizing c <;> simp [List.getLast?_cons, *]

namespace Tree

/-- Whether a tree is the code of a Boolean: a leaf, or a pair of leaves. -/
def isBoolCode (t : Tree) : Bool :=
  match t with
  | .nil => true
  | .pair a b => !a.root && !b.root

theorem isBoolCode_eq_true_iff {t : Tree} : t.isBoolCode = true ↔ ∃ b : Bool, ⌜b⌝ₜ = t := by
  rcases t with _ | ⟨⟨⟩, _ | ⟨⟨⟩, _, _⟩, _ | ⟨⟨⟩, _, _⟩⟩ <;> simp [isBoolCode, Bool.exists_bool]

/-- Whether a tree is the code of a natural number: the code of a list of Booleans whose last
element, if any, is `true`. -/
def isNatCode (t : Tree) : Bool :=
  t.spine.foldl (fun b e => b && e.isBoolCode) true && t.spine.foldl (fun _ e => e.root) true

theorem isNatCode_eq_true_iff {t : Tree} : t.isNatCode = true ↔ (decode ℕ t).Dom := by
  have hlast (xs : List Bool) : (xs.map (encode Tree)).foldl (fun _ e => e.root) true =
      xs.getLast?.getD true := by
    simp only [List.foldl_map, root_encode_bool, foldl_last_eq_getLastD]
  rw [UniqueEncoding.dom_decode_iff, isNatCode, Bool.and_eq_true, foldl_and_eq_true]
  simp only [isBoolCode_eq_true_iff]
  rw [← exists_encode_list_eq_iff]
  constructor
  · rintro ⟨⟨xs, rfl⟩, h⟩
    rw [spine_encode_list, hlast, ← BitList.exists_bits_eq_iff] at h
    obtain ⟨n, rfl⟩ := h
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨n.bits, rfl⟩, ?_⟩
    rw [encode_nat_tree, spine_encode_list, hlast, ← BitList.exists_bits_eq_iff]
    exact ⟨n, rfl⟩

theorem hasProgramIn_isBoolCode : HasProgramIn isBoolCode hole(⊢ program) IsO(fun _ => 1)
    IsO(fun t => ⌜t⌝ₜ.size) := by
  abstract_hole program using programIsBoolCode
  fill_hole program in source_fun_prop

attribute [local program] hasProgramIn_isBoolCode in
theorem hasProgramIn_isNatCode : HasProgramIn isNatCode hole(⊢ program) IsO(fun t => ⌜t⌝ₜ.size)
    IsO(fun t => ⌜t⌝ₜ.size) := by
  abstract_hole program using programIsNatCode
  fill_hole program in source_fun_prop

end Tree

namespace TreeMachine

/-- The codes of natural numbers are recognized in polynomial time. -/
theorem dom_decode_nat_mem_p : (fun t : Tree => (decode ℕ t).Dom) ∈ P .sizeCostTree :=
  P.of_decides Tree.hasProgramIn_isNatCode.isPoly.mem_fp_sizeCost fun _ =>
    Tree.isNatCode_eq_true_iff

/-- The codes of lists are recognized in polynomial time when the codes of their elements are. -/
theorem dom_decode_list_mem_p {α : Type*} [UniqueEncoding Tree α]
    (h : (fun t : Tree => (decode α t).Dom) ∈ P .sizeCostTree) :
    (fun t : Tree => (decode (List α) t).Dom) ∈ P .sizeCostTree := by
  obtain ⟨check, hcheck, hdec⟩ := h
  obtain ⟨q, hq⟩ := exists_hasProgramIn_of_mem_fp hcheck
  refine P.of_decides (f := fun t => t.spine.foldl (fun b e => b && check e) true)
    (by model_fun_prop) fun t => ?_
  simp only [foldl_and_eq_true, UniqueEncoding.dom_decode_iff, exists_encode_list_eq_iff]
  exact forall₂_congr fun e _ => (hdec e).trans UniqueEncoding.dom_decode_iff

end TreeMachine

end Complexity
