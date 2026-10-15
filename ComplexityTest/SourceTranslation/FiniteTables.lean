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

example : Nonempty (Implementation (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1))) :=
  ⟨by source_fun_prop using tabulate⟩

-- Ordinary rule matching handles index aliases, including inside an ofFn callback.
private abbrev Index (n : ℕ) := Fin n

example : Nonempty (Implementation (fun n : ℕ => List.ofFn (fun i : Index n => i.val + 1))) :=
  ⟨by source_fun_prop using tabulate⟩

example : True := by
  fail_if_success
    have : Nonempty (Implementation (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1))) :=
      ⟨by source_fun_prop⟩
  trivial

-- Reading a stored tuple stays automatic; the selected scope does not rebuild stored fields.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2),
      ∀ x, impl.bounds.time x = 1 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp [source_bounds]

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2),
      ∀ x, impl.bounds.time x = 1 := by
  refine ⟨by source_fun_prop using tabulate, ?_⟩
  simp [source_bounds]

def identityWires (n : ℕ) : Σ n, Fin n → Fin n := ⟨n, id⟩

example : Nonempty (Implementation identityWires) := ⟨by source_fun_prop using tabulate⟩

def appendEntry (x : Σ n, (Fin n → ℕ) × ℕ) : Σ n, Fin n → ℕ :=
  ⟨x.1 + 1, Fin.snoc x.2.1 x.2.2⟩

example : Nonempty (Implementation appendEntry) := ⟨by source_fun_prop⟩

def appendWire (x : Σ n, Σ m, (Fin n → Fin m) × Fin m) : Σ n, Σ m, Fin n → Fin m :=
  ⟨x.1 + 1, x.2.1, Fin.snoc x.2.2.1 x.2.2.2⟩

example : Nonempty (Implementation appendWire) := ⟨by source_fun_prop⟩

def appendTables (x : Σ n, Σ m, (Fin n → ℕ) × (Fin m → ℕ)) : Σ n, Fin n → ℕ :=
  ⟨x.1 + x.2.1, Fin.append x.2.2.1 x.2.2.2⟩

example : Nonempty (Implementation appendTables) := ⟨by source_fun_prop⟩

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

example : Nonempty (Implementation shiftWire) := ⟨by source_fun_prop⟩

section FinAppendImplementation

variable {ρ : Type*} {α : ρ → Type*}
  [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
  {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {g : (e : ρ) → Fin (m e) → α e}
  (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hg : Implementation (fun e => ⌜g e⌝ₜ))

-- Both precise budgets and the actual supplied programs survive dependent table concatenation.
example : (hf.finAppend hg).bounds =
    ⟨fun e => hf.bounds.time e + hg.bounds.time e + 26 * n e + 16,
     fun e => max (hf.bounds.peak e)
       (max (hg.bounds.peak e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))⟩ := by
  simp [source_bounds, appendBounds, List.length_ofFn, encode_fin_function_codes, Nat.add_assoc]

example : (hf.finAppend hg).program = (fun v => do
    let a ← hf.program v
    let b ← hg.program v
    List.Code.append a b) := rfl

-- Native fun_prop and fixed-budget source translation both use the registered constructor.
example : Nonempty (Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ)) := ⟨by fun_prop⟩

example :
    (show Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) from by source_fun_prop).program =
      (hf.finAppend hg).program := rfl

end FinAppendImplementation

-- Only the first table is traversed; a stored second table is not regenerated.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) =>
      ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ),
      ∀ x, impl.bounds.time x = 26 * x.1 + 22 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp [source_bounds]
  omega

-- Selecting the enumeration scope must preserve the polymorphic append implementation.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) =>
      ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ),
      ∀ x, impl.bounds.time x = 26 * x.1 + 22 := by
  refine ⟨by source_fun_prop using tabulate, ?_⟩
  simp [source_bounds]
  omega

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, (Fin n → α) × α =>
      ⌜Fin.snoc x.2.1 x.2.2⌝ₜ), ∀ x, impl.bounds.time x = 26 * x.1 + 22 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp [source_bounds]
  omega

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : Σ n, (Fin n → α) × α =>
      ⌜Fin.snoc x.2.1 x.2.2⌝ₜ), ∀ x, impl.bounds.time x = 26 * x.1 + 22 := by
  refine ⟨by source_fun_prop using tabulate, ?_⟩
  simp [source_bounds]
  omega

def successorWires (n : ℕ) : Σ n, Fin n → Fin (n + 1) := ⟨n, Fin.castSucc⟩

example : Nonempty (Implementation successorWires) := ⟨by source_fun_prop using tabulate⟩

-- A change of index bound keeps the stored table; it is not pointwise table generation.
example : ∃ impl : Implementation (fun x : Σ n, Σ k, Fin n → Fin k =>
    ⌜Fin.castSucc ∘ x.2.2⌝ₜ), ∀ x, impl.bounds.time x = 2 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp [source_bounds]

def identityCircuit (n : ℕ) : Σ n, Circuit .booleanAlgebra n n := ⟨n, .id _ n⟩

example : Nonempty (Implementation identityCircuit) := ⟨by source_fun_prop using tabulate⟩

def positions {α : Type*} (xs : List α) : List ℕ := List.ofFn (fun i : Fin xs.length => i.val)

-- Choose enumeration for this function once. Callers, including nested calls, need no permission.
@[local source using tabulate] theorem positions_source {α : Type*} :
    positions (α := α) = (fun xs => List.ofFn (fun i : Fin xs.length => i.val)) := rfl

example : Nonempty (Implementation (fun xs : List Bool => (positions xs).reverse)) :=
  ⟨by source_fun_prop⟩

-- Ordinary constructors retain runtime dimensions and wire types.
def complementLayer (xs : List Unit) : List (Σ n, Circuit .booleanAlgebra n 1) :=
  let n := xs.length
  List.ofFn (fun i : Fin n =>
    ⟨n, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩)

noncomputable example : Implementation complementLayer := by source_fun_prop using tabulate

noncomputable example {α : Type*} [UniqueEncoding Tree α] : Implementation (positions (α := α)) := by
  source_fun_prop

-- Two dependent table lookups compose inside a newly generated table.
def composeWires (x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)) :
    Σ n, Σ m, Fin n → Fin m := ⟨x.1, x.2.2.1, x.2.2.2.2 ∘ x.2.2.2.1⟩

example : Nonempty (Implementation composeWires) := ⟨by source_fun_prop using tabulate⟩

attribute [local fun_prop] Implementation.finComp in
theorem composeWires_ftisp :
    composeWires ∈ FTISP .tree (fun n => n ^ 3) (fun n => n ^ 2) := by
  model_fun_prop
  all_goals
    simp only [Function.comp_apply, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals first
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
    | apply Dominated.of_le
      rintro ⟨n, k, m, f, g⟩
      have hf := size_encode_fin_comp_le f g
      have hpos := Tree.size_pos ⌜(n, k, m, f, g)⌝ₜ
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self] at *
      nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) ⌜(n, k, m, f, g)⌝ₜ.size]

-- A represented table and a single callback implement one algorithm for every runtime index.
-- Pointwise existence must not be mistaken for such a callback.
example (f : ℕ → ℕ → Bool) (_hf : ∀ n, Implementation (f n)) : True := by
  fail_if_success
    have : Nonempty (Implementation (fun n => List.ofFn (fun i : Fin n => f n i.val))) :=
      ⟨by source_fun_prop using tabulate⟩
  trivial

end ComplexityTest.SourceTranslation.FiniteTables
