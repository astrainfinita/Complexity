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
  HasProgram (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _ _)

-- Ordinary rule matching handles index aliases, including inside an ofFn callback.
private abbrev Index (n : ℕ) := Fin n

example := (by source_fun_prop using tabulate :
  HasProgram (fun n : ℕ => List.ofFn (fun i : Index n => i.val + 1)) _ _ _)

example : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgram (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) _ _ _)
  trivial

-- Reading a stored tuple stays automatic; the selected scope does not rebuild stored fields.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgram (fun x : Σ n, Fin n → α => List.ofFn x.2) _ (fun _ => 1) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  HasProgram (fun x : Σ n, Fin n → α => List.ofFn x.2) _ (fun _ => 1) _)

def identityWires (n : ℕ) : Σ n, Fin n → Fin n := ⟨n, id⟩

example := (by source_fun_prop using tabulate : HasProgram identityWires _ _ _)

def appendEntry (x : Σ n, (Fin n → ℕ) × ℕ) : Σ n, Fin n → ℕ :=
  ⟨x.1 + 1, Fin.snoc x.2.1 x.2.2⟩

example := (by source_fun_prop : HasProgram appendEntry _ _ _)

def appendWire (x : Σ n, Σ m, (Fin n → Fin m) × Fin m) : Σ n, Σ m, Fin n → Fin m :=
  ⟨x.1 + 1, x.2.1, Fin.snoc x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : HasProgram appendWire _ _ _)

def appendTables (x : Σ n, Σ m, (Fin n → ℕ) × (Fin m → ℕ)) : Σ n, Fin n → ℕ :=
  ⟨x.1 + x.2.1, Fin.append x.2.2.1 x.2.2.2⟩

example := (by source_fun_prop : HasProgram appendTables _ _ _)

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

example := (by source_fun_prop : HasProgram shiftWire _ _ _)

section FinAppendImplementation

variable {ρ : Type*} {α : ρ → Type*}
  [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
  {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {g : (e : ρ) → Fin (m e) → α e}
  {qf qg : Value → Code Value} {tf pf tg pg : ρ → ℕ}
  (hf : HasProgram (fun e => ⌜f e⌝ₜ) qf tf pf) (hg : HasProgram (fun e => ⌜g e⌝ₜ) qg tg pg)
include hf hg

-- The growth adds the supplied growths and a traversal of the first table only.
example : HasProgram (fun e => ⌜Fin.append (f e) (g e)⌝ₜ)
    (fun v => do
      let a ← qf v
      let b ← qg v
      List.Code.append a b)
    (fun e => tf e + (tg e + (n e + 1)))
    (fun e => max (pf e) (max (pg e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))) :=
  hf.finAppend hg

-- Native fun_prop and source translation both use the registered constructor.
example := (by fun_prop : HasProgram (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) _ _ _)

example := (by source_fun_prop : HasProgram (fun e => ⌜Fin.append (f e) (g e)⌝ₜ)
  (fun v => do let a ← qf v; let b ← qg v; List.Code.append a b) _ _)

end FinAppendImplementation

-- Only the first table is traversed; a stored second table is not regenerated.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgram (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ) _
    (fun x => 1 + (1 + (x.1 + 1))) _)

-- Selecting the enumeration scope must preserve the polymorphic append implementation.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  HasProgram (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) => ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ) _
    (fun x => 1 + (1 + (x.1 + 1))) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgram (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ) _
    (fun x => 1 + (1 + 0) + x.1 + 1) _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using tabulate :
  HasProgram (fun x : Σ n, (Fin n → α) × α => ⌜Fin.snoc x.2.1 x.2.2⌝ₜ) _
    (fun x => 1 + (1 + 0) + x.1 + 1) _)

def successorWires (n : ℕ) : Σ n, Fin n → Fin (n + 1) := ⟨n, Fin.castSucc⟩

example := (by source_fun_prop using tabulate : HasProgram successorWires _ _ _)

-- A change of index bound keeps the stored table; it is not pointwise table generation.
example := (by source_fun_prop :
  HasProgram (fun x : Σ n, Σ k, Fin n → Fin k => ⌜Fin.castSucc ∘ x.2.2⌝ₜ) _ (fun _ => 1) _)

def identityCircuit (n : ℕ) : Σ n, Circuit .booleanAlgebra n n := ⟨n, .id _ n⟩

example := (by source_fun_prop using tabulate : HasProgram identityCircuit _ _ _)

def positions {α : Type*} (xs : List α) : List ℕ := List.ofFn (fun i : Fin xs.length => i.val)

-- Choose enumeration for this function once. Callers, including nested calls, need no permission.
@[local source using tabulate] theorem positions_source {α : Type*} :
    positions (α := α) = (fun xs => List.ofFn (fun i : Fin xs.length => i.val)) := rfl

noncomputable example := (by source_fun_prop :
  HasProgram (fun xs : List Bool => (positions xs).reverse) _ _ _)

-- Ordinary constructors retain runtime dimensions and wire types.
def complementLayer (xs : List Unit) : List (Σ n, Circuit .booleanAlgebra n 1) :=
  let n := xs.length
  List.ofFn (fun i : Fin n =>
    ⟨n, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩)

noncomputable example := (by source_fun_prop using tabulate : HasProgram complementLayer _ _ _)

noncomputable example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  HasProgram (positions (α := α)) _ _ _)

-- Two dependent table lookups compose inside a newly generated table.
def composeWires (x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)) :
    Σ n, Σ m, Fin n → Fin m := ⟨x.1, x.2.2.1, x.2.2.2.2 ∘ x.2.2.2.1⟩

example := (by source_fun_prop using tabulate : HasProgram composeWires _ _ _)

attribute [local fun_prop] HasProgram.fin_comp in
theorem composeWires_ftisp :
    composeWires ∈ FTISP .tree (fun n => n ^ 3) (fun n => n ^ 2) := by
  model_fun_prop
  all_goals dominated

-- A represented table and a single callback implement one algorithm for every runtime index.
-- Pointwise existence must not be mistaken for such a callback.
example (f : ℕ → ℕ → Bool) (program : ℕ → Value → Code Value)
    (_hf : ∀ n, HasProgram (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop using tabulate :
      HasProgram (fun n => List.ofFn (fun i : Fin n => f n i.val)) _ _ _)
  trivial

end ComplexityTest.SourceTranslation.FiniteTables
