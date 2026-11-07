/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import Complexity.Models.Circuit.TreeEncoding
import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding
import Complexity.Classes.Functions.Basic

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

namespace ComplexityTest.SourceTranslation.FiniteTables

example := (by source_fun_prop using tabulate :
  HasProgramInO (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _ _)

-- Ordinary rule matching handles index aliases, including inside an ofFn callback.
private abbrev Index (n : ℕ) := Fin n

example := (by source_fun_prop using tabulate :
  HasProgramInO (fun n : ℕ => List.ofFn (fun i : Index n => i.val + 1)) _ _ _)

example : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgramInO (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _ _)
  trivial

-- Reading a stored tuple stays automatic; the selected scope does not rebuild stored fields.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, Fin n → α => List.ofFn x.2) _ (fun _ => 1) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  HasProgramInO (fun x : Σ n, Fin n → α => List.ofFn x.2) _ (fun _ => 1) _)

def identityWires (n : ℕ) : Σ n, Fin n → Fin n := ⟨n, id⟩

example := (by source_fun_prop using tabulate : HasProgramInO identityWires _ _ _)

def appendEntry (x : Σ n, (Fin n → ℕ) × ℕ) : Σ n, Fin n → ℕ :=
  ⟨x.1 + 1, Fin.snoc x.2.1 x.2.2⟩

example := (by source_fun_prop : HasProgramInO appendEntry _ _ _)

def appendWire (x : Σ n, Σ m, (Fin n → Fin m) × Fin m) : Σ n, Σ m, Fin n → Fin m :=
  ⟨x.1 + 1, x.2.1, Fin.snoc x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : HasProgramInO appendWire _ _ _)

def appendTables (x : Σ n, Σ m, (Fin n → ℕ) × (Fin m → ℕ)) : Σ n, Fin n → ℕ :=
  ⟨x.1 + x.2.1, Fin.append x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : HasProgramInO appendTables _ _ _)

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

example := (by source_fun_prop : HasProgramInO shiftWire _ _ _)

section FinAppendImplementation

variable {ρ : Type*} {α : ρ → Type*}
  [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
  {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {g : (e : ρ) → Fin (m e) → α e}
  {qf qg : Value → Code Value} {tf pf tg pg : ρ → ℕ}
  (hf : HasProgramInO f qf tf pf) (hg : HasProgramInO g qg tg pg)
include hf hg

-- Appending tables appends their lists: the supplied growths, a pair and a traversal of the
-- first table only.
example : ∃ q p, HasProgramInO (fun e => Fin.append (f e) (g e)) q
    (fun e => tf e + tg e + n e + 2) p := by
  refine ⟨?q, ?p, ?h⟩
  case h =>
    source_fun_prop

end FinAppendImplementation

-- Only the first table is traversed; a stored second table is not regenerated.
example {α : Type*} [UniqueEncoding Tree α] : ∃ q p, HasProgramInO
    (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ) q
    (fun x => x.1 + 4) p := by
  refine ⟨?q, ?p, ?h⟩
  case h =>
    source_fun_prop

-- Selecting the enumeration scope must preserve the polymorphic append implementation.
example {α : Type*} [UniqueEncoding Tree α] : ∃ q p, HasProgramInO
    (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ) q
    (fun x => x.1 + 4) p := by
  refine ⟨?q, ?p, ?h⟩
  case h =>
    source_fun_prop using tabulate

example {α : Type*} [UniqueEncoding Tree α] : ∃ q p, HasProgramInO
    (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ) q (fun x => x.1 + 4) p := by
  refine ⟨?q, ?p, ?h⟩
  case h =>
    source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] : ∃ q p, HasProgramInO
    (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ) q (fun x => x.1 + 4) p := by
  refine ⟨?q, ?p, ?h⟩
  case h =>
    source_fun_prop using tabulate

def successorWires (n : ℕ) : Σ n, Fin n → Fin (n + 1) := ⟨n, Fin.castSucc⟩

example := (by source_fun_prop using tabulate : HasProgramInO successorWires _ _ _)

-- A change of index bound keeps the stored table; it is not pointwise table generation.
example := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, Σ k, Fin n → Fin k => ⌜Fin.castSucc ∘ x.2.2⌝ₜ) _ (fun _ => 1) _)

def identityCircuit (n : ℕ) : Σ n, Circuit .booleanAlgebra n n := ⟨n, .id _ n⟩

example := (by source_fun_prop using tabulate : HasProgramInO identityCircuit _ _ _)

def positions {α : Type*} (xs : List α) : List ℕ := List.ofFn (fun i : Fin xs.length => i.val)

-- Choose enumeration for this function once. Callers, including nested calls, need no permission.
@[local program using tabulate] theorem positions_source {α : Type*} :
    positions (α := α) = (fun xs => List.ofFn (fun i : Fin xs.length => i.val)) := rfl

noncomputable example := (by source_fun_prop :
  HasProgramInO (fun xs : List Bool => (positions xs).reverse) _ _ _)

-- Ordinary constructors retain runtime dimensions and wire types.
def complementLayer (xs : List Unit) : List (Σ n, Circuit .booleanAlgebra n 1) :=
  let n := xs.length
  List.ofFn (fun i : Fin n =>
    ⟨n, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩)

noncomputable example := (by source_fun_prop using tabulate : HasProgramInO complementLayer _ _ _)

noncomputable example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgramInO (positions (α := α)) _ _ _)

-- Two dependent table lookups compose inside a newly generated table.
def composeWires (x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)) :
    Σ n, Σ m, Fin n → Fin m := ⟨x.1, x.2.2.1, x.2.2.2.2 ∘ x.2.2.2.1⟩

example := (by source_fun_prop using tabulate : HasProgramInO composeWires _ _ _)

attribute [local fun_prop] HasProgramInO.fin_comp in
theorem composeWires_fdtisp :
    composeWires ∈ FDTISP .tree (fun n => n ^ 3) (fun n => n ^ 2) := by
  model_fun_prop

-- A represented table and a single callback implement one algorithm for every runtime index.
-- Pointwise existence must not be mistaken for such a callback.
example (f : ℕ → ℕ → Bool) (program : ℕ → Value → Code Value)
    (_hf : ∀ n, HasProgramInO (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop using tabulate :
      HasProgramInO (fun n => List.ofFn (fun i : Fin n => f n i.val)) _ _ _)
  trivial

-- Neither a class method at an index nor a local function without a code is a table read; the
-- missing implementation is reported.
/-- error: source translation: `Fin.add` needs a selected implementation -/
#guard_msgs (substring := true) in
example := (by source_fun_prop : HasProgramInO (fun x : Fin 3 × Fin 3 => x.1 + x.2) _ _ _)

/-- error: source translation: `f` needs an implementation -/
#guard_msgs (substring := true) in
example (f : ℕ → ℕ) := (by source_fun_prop : HasProgramInO (fun n : ℕ => f n) _ _ _)

end ComplexityTest.SourceTranslation.FiniteTables
