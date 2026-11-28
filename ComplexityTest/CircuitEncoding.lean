/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.Circuit.TreeEncoding
import Complexity.Models.TreeMachine.Language.Derive
import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding

open Complexity FirstOrder

namespace Complexity.CircuitEncodingTest

universe u v

section Generic

variable {L : Language.{u, v}} [∀ k, UniqueEncoding Tree (L.Functions k)] {n m k : ℕ}

example : UniqueEncoding Tree (Circuit L n m) := inferInstance

-- Guards the tree code layout of `Circuit`: wire tables are stored as `FinVector`s.
example (select : Fin m → Fin n) :
    encode Tree (Circuit.outputs select : Circuit L n m) =
      .pair .nil (encode Tree (FinVector.ofFn select)) := rfl

example (op : L.Functions k) (args : Fin k → Fin n) (next : Circuit L (n + 1) m) :
    encode Tree (Circuit.gate op args next) =
      .pair (.pair .nil .nil)
        (.pair (encode Tree k) (.pair (encode Tree op)
          (.pair (encode Tree (FinVector.ofFn args)) (encode Tree next)))) := rfl

example (c : Circuit L n m) (t : Tree) :
    c ∈ decode (Circuit L n m) t ↔ encode Tree c = t := UniqueEncoding.mem_decode_iff

example (c : Circuit L n m) : decode (Circuit L n m) (encode Tree c) = Part.some c :=
  UniqueEncoding.decode_encode c

-- Guards that `simp` does not unfold `⌜c⌝ₜ` to `treeEncode c` on a circuit variable.
example (c : Circuit L n m) (h : ⌜c⌝ₜ.size = 0) : ⌜c⌝ₜ.size = 0 := by
  fail_if_success simp
  exact h

end Generic

section Boolean

example : UniqueEncoding Tree (Σ n, Circuit .booleanAlgebra n 1) := inferInstance

example (n : ℕ) (c : Circuit .booleanAlgebra n 1) :
    encode Tree (⟨n, c⟩ : Σ n, Circuit .booleanAlgebra n 1) = encode Tree (n, c) := by simp

example (p : Σ n, Circuit .booleanAlgebra n 1) :
    decode (Σ n, Circuit .booleanAlgebra n 1) (encode Tree p) = Part.some p :=
  UniqueEncoding.decode_encode p

end Boolean

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

private theorem missingArgument : decode (FinVector (Fin 1) 1) Tree.nil = Part.none := by
  apply Part.eq_none_iff.mpr
  intro f hf
  have h := congrArg Tree.listLength (UniqueEncoding.mem_decode_iff.mp hf)
  simp [encode_finVector] at h

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
