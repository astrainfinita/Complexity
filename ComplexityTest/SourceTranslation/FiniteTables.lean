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

namespace ComplexityTest.SourceTranslation.FiniteTables

example := (by source_fun_prop using tabulate :
  Implementation (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _)

-- Ordinary rule matching handles index aliases, including inside an ofFn callback.
private abbrev Index (n : ℕ) := Fin n

example := (by source_fun_prop using tabulate :
  Implementation (fun n : ℕ => List.ofFn (fun i : Index n => i.val + 1)) _ _)

example : True := by
  fail_if_success
    have := (by source_fun_prop :
      Implementation (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _)
  trivial

-- Reading a stored tuple stays automatic; the selected scope does not rebuild stored fields.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2) (fun _ => 1) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2) (fun _ => 1) _)

def identityWires (n : ℕ) : Σ n, Fin n → Fin n := ⟨n, id⟩

example := (by source_fun_prop using tabulate : Implementation identityWires _ _)

def appendEntry (x : Σ n, (Fin n → ℕ) × ℕ) : Σ n, Fin n → ℕ :=
  ⟨x.1 + 1, Fin.snoc x.2.1 x.2.2⟩

example := (by source_fun_prop : Implementation appendEntry _ _)

def appendWire (x : Σ n, Σ m, (Fin n → Fin m) × Fin m) : Σ n, Σ m, Fin n → Fin m :=
  ⟨x.1 + 1, x.2.1, Fin.snoc x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : Implementation appendWire _ _)

def appendTables (x : Σ n, Σ m, (Fin n → ℕ) × (Fin m → ℕ)) : Σ n, Fin n → ℕ :=
  ⟨x.1 + x.2.1, Fin.append x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : Implementation appendTables _ _)

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

example := (by source_fun_prop : Implementation shiftWire _ _)

section FinAppendImplementation

variable {ρ : Type*} {α : ρ → Type*}
  [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
  {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {g : (e : ρ) → Fin (m e) → α e}
  {tf pf tg pg : ρ → ℕ}
  (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf) (hg : Implementation (fun e => ⌜g e⌝ₜ) tg pg)
include hf hg

-- The growth adds the supplied growths and a traversal of the first table only.
example : Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) (fun e => tf e + (tg e + (n e + 1)))
    (fun e => max (pf e) (max (pg e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))) := hf.finAppend hg

example : (hf.finAppend hg).program = (fun v => do
    let a ← hf.program v
    let b ← hg.program v
    List.Code.append a b) := rfl

-- Native fun_prop and source translation both use the registered constructor.
example := (by fun_prop : Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) _ _)

example : (by source_fun_prop : Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) _ _).program =
    (hf.finAppend hg).program := rfl

end FinAppendImplementation

-- Only the first table is traversed; a stored second table is not regenerated.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  Implementation (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ)
    (fun x => 1 + (1 + (x.1 + 1))) _)

-- Selecting the enumeration scope must preserve the polymorphic append implementation.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  Implementation (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ)
    (fun x => 1 + (1 + (x.1 + 1))) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  Implementation (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ)
    (fun x => 1 + (1 + 0) + x.1 + 1) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  Implementation (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ)
    (fun x => 1 + (1 + 0) + x.1 + 1) _)

def successorWires (n : ℕ) : Σ n, Fin n → Fin (n + 1) := ⟨n, Fin.castSucc⟩

example := (by source_fun_prop using tabulate : Implementation successorWires _ _)

-- A change of index bound keeps the stored table; it is not pointwise table generation.
example := (by source_fun_prop :
  Implementation (fun x : Σ n, Σ k, Fin n → Fin k => ⌜Fin.castSucc ∘ x.2.2⌝ₜ) (fun _ => 1) _)

def identityCircuit (n : ℕ) : Σ n, Circuit .booleanAlgebra n n := ⟨n, .id _ n⟩

example := (by source_fun_prop using tabulate : Implementation identityCircuit _ _)

def positions {α : Type*} (xs : List α) : List ℕ := List.ofFn (fun i : Fin xs.length => i.val)

-- Choose enumeration for this function once. Callers, including nested calls, need no permission.
@[local source using tabulate] theorem positions_source {α : Type*} :
    positions (α := α) = (fun xs => List.ofFn (fun i : Fin xs.length => i.val)) := rfl

noncomputable example := (by source_fun_prop :
  Implementation (fun xs : List Bool => (positions xs).reverse) _ _)

-- Ordinary constructors retain runtime dimensions and wire types.
def complementLayer (xs : List Unit) : List (Σ n, Circuit .booleanAlgebra n 1) :=
  let n := xs.length
  List.ofFn (fun i : Fin n =>
    ⟨n, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩)

noncomputable example := (by source_fun_prop using tabulate : Implementation complementLayer _ _)

noncomputable example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  Implementation (positions (α := α)) _ _)

-- Two dependent table lookups compose inside a newly generated table.
def composeWires (x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)) :
    Σ n, Σ m, Fin n → Fin m := ⟨x.1, x.2.2.1, x.2.2.2.2 ∘ x.2.2.2.1⟩

example := (by source_fun_prop using tabulate : Implementation composeWires _ _)

attribute [local fun_prop] Implementation.finComp in
theorem composeWires_ftisp :
    composeWires ∈ FTISP .tree (fun n => n ^ 3) (fun n => n ^ 2) := by
  model_fun_prop
  all_goals dominated

-- A represented table and a single callback implement one algorithm for every runtime index.
-- Pointwise existence must not be mistaken for such a callback.
example (f : ℕ → ℕ → Bool) (_hf : ∀ n, Implementation (f n) (fun _ => 1) (fun _ => 1)) :
    True := by
  fail_if_success
    have := (by source_fun_prop using tabulate :
      Implementation (fun n => List.ofFn (fun i : Fin n => f n i.val)) _ _)
  trivial

end ComplexityTest.SourceTranslation.FiniteTables
