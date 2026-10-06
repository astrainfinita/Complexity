/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.Circuit.TreeEncoding

open Complexity TreeProgram TreeProgram.Code FirstOrder

namespace Complexity.CircuitEncodingTest

universe u v

section Generic

variable {L : Language.{u, v}} [∀ k, UniqueEncoding Tree (L.Functions k)] {n m k : ℕ}

example : UniqueEncoding Tree (Circuit L n m) := inferInstance

example (select : Fin m → Fin n) :
    encode Tree (Circuit.outputs select : Circuit L n m) = .pair .nil (encode Tree select) := rfl

example (op : L.Functions k) (args : Fin k → Fin n) (next : Circuit L (n + 1) m) :
    encode Tree (Circuit.gate op args next) =
      .pair (.pair .nil .nil)
        (.pair (encode Tree k) (.pair (encode Tree op)
          (.pair (encode Tree args) (encode Tree next)))) := rfl

example (c : Circuit L n m) (t : Tree) :
    c ∈ decode (Circuit L n m) t ↔ encode Tree c = t := UniqueEncoding.mem_decode_iff

example (c : Circuit L n m) : decode (Circuit L n m) (encode Tree c) = Part.some c :=
  UniqueEncoding.decode_encode c

def rebuild (x : Value) : Code Value :=
  Circuit.Code.matchOn x Circuit.Code.outputs Circuit.Code.gate

example (c : Circuit L n m) : (rebuild .input).Computes (encode Tree c) (encode Tree c) := by
  cases c <;> simp [computes_iff, rebuild]

example (op : L.Functions k) (args : Fin k → Fin n) (next : Circuit L (n + 1) m) :
    (Circuit.Code.matchOn .input (fun _ => pure .nil) (fun _ _ _ c => pure c)).Computes
      (encode Tree (Circuit.gate op args next)) (encode Tree next) := by
  simp [computes_iff]

end Generic

abbrev language : Language where
  Functions k := Fin (k + 1)
  Relations _ := Empty

def shared : Circuit language 0 2 :=
  .gate (k := 0) 0 Fin.elim0 (.gate (k := 2) 2 ![0, 0] (.outputs ![0, 1]))

example : UniqueEncoding Tree (Circuit language 0 2) := inferInstance

example : (encode Tree shared).left = Tree.pair .nil .nil := by decide

example : encode Tree (Circuit.outputs Fin.elim0 : Circuit language 0 0) =
    Tree.pair .nil .nil := rfl

private theorem invalidSymbol : decode (Fin 1) (encode Tree (1 : ℕ)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro a ha
  have h : a.val = 1 := by
    simpa only [UniqueEncoding.mem_decode_iff, encode_fin, UniqueEncoding.encode_inj] using ha
  have := a.isLt
  omega

example : decode (Circuit language 0 0)
    (Tree.pair (.pair .nil .nil) (.pair (encode Tree (0 : ℕ))
      (.pair (encode Tree (1 : ℕ)) (.pair .nil (.pair .nil .nil))))) = Part.none := by
  change (Circuit.treeDecode _ : Part (Circuit language 0 0)) = _
  simp only [Circuit.treeDecode, UniqueEncoding.decode_encode, Part.bind_some]
  change (decode (Fin 1) (encode Tree (1 : ℕ))).bind _ = _
  rw [invalidSymbol, Part.bind_none]

private theorem missingArgument : decode (Fin 1 → Fin 1) Tree.nil = Part.none := by
  apply Part.eq_none_iff.mpr
  intro f hf
  have h := congrArg Tree.listLength (UniqueEncoding.mem_decode_iff.mp hf)
  simp at h

example : decode (Circuit language 1 0)
    (Tree.pair (.pair .nil .nil) (.pair (encode Tree (1 : ℕ))
      (.pair (encode Tree (0 : Fin 2)) (.pair .nil (.pair .nil .nil))))) = Part.none := by
  change (Circuit.treeDecode _ : Part (Circuit language 1 0)) = _
  simp only [Circuit.treeDecode, UniqueEncoding.decode_encode, Part.bind_some]
  rw [missingArgument, Part.bind_none]

@[tree_encoding]
structure Dependent (α : Type*) (F : α → Type*) where
  index : α
  value : F index

example {α : Type*} {F : α → Type*} [UniqueEncoding Tree α]
    [∀ a, UniqueEncoding Tree (F a)] (a : α) (x : F a) :
    encode Tree (Dependent.mk a x) = .pair (encode Tree a) (encode Tree x) := rfl

@[tree_encoding]
inductive Reordered (α : Type*) : ℕ → ℕ → Type _ where
  | mk {m n : ℕ} (value : α) (select : Fin m → Fin n) : Reordered α n m

example {α : Type*} [UniqueEncoding Tree α] {n m : ℕ} (a : α) (s : Fin m → Fin n) :
    encode Tree (Reordered.mk a s) = .pair (encode Tree a) (encode Tree s) := rfl

run_cmd do
  for name in [``Circuit.treeEncoding, ``Dependent.treeEncoding, ``Reordered.treeEncoding] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on an unfinished proof"

end Complexity.CircuitEncodingTest
