/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ComplexityTest.SourceTranslation.SpecComparison
import Complexity.Resources.Circuit.Program
import Complexity.Models.Circuit.Composition

/-! # Source translation and complexity-bound regressions -/

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

open ComplexityTest.SourceTranslation.SpecComparison

namespace ComplexityTest.SourceTranslation.Examples

attribute [local program] hasProgramIn_duplicate

-- A shared let computes the reversal once; the unshared source reverses twice.
example : HasProgramInO sharePlain hole(⊢ program)
    (fun xs => ⌜xs⌝ₜ.size + (0 + (0 + 1) + (xs.reverse.length + 1)))
    (fun xs => max ⌜xs⌝ₜ.size (max ⌜xs.reverse⌝ₜ.size ⌜(xs.reverse, xs.reverse)⌝ₜ.size)) := by
  fill_hole program in source_fun_prop

example : HasProgramInO unshared hole(⊢ program)
    (fun xs => ⌜xs⌝ₜ.size + (⌜xs⌝ₜ.size + 1) + (xs.reverse.length + 1))
    (fun xs => max (max ⌜xs⌝ₜ.size (max ⌜xs⌝ₜ.size ⌜(xs.reverse, xs.reverse)⌝ₜ.size))
      ⌜(xs.reverse, xs.reverse)⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Local implementations also work, without exposing or naming the model implementation.
example {f : List Bool → List Bool} {pf : Value → Code Value} {t p : List Bool → ℕ}
    (_hf : HasProgramInO f pf t p) :
    HasProgramInO (fun xs => (f xs).reverse) (fun v => pf v >>= List.Code.reverse)
      (fun xs => t xs + ⌜f xs⌝ₜ.size) (fun xs => max (p xs) ⌜f xs⌝ₜ.size) := by
  source_fun_prop

-- Eliminating an unused let is an allowed optimization: certify the identity implementation.
example : HasProgramInO (fun xs : List Bool => let _ys := xs.reverse; xs) hole(⊢ program)
    (fun _ => 0)
    (fun _ => 0) := by
  fill_hole program in source_fun_prop

-- Match existing operations instead of generating arbitrary new append expressions.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, FinVector α n × Fin n => x.2.1.get x.2.2) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun x : List α × ℕ => x.1[x.2]?) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, FinVector (List Bool) n × Fin n => (x.2.1.get x.2.2).reverse)
      _ _ _)

example {α : Type*} [UniqueEncoding Tree α] (n : ℕ) := (by source_fun_prop :
    HasProgramInO (fun x : FinVector α n × Fin n => x.1.get x.2) _ _ _)

example := (by source_fun_prop : HasProgramInO
    (fun x : Σ n, Σ k, FinVector (Fin k) n × Fin n => (x.2.2.1.get x.2.2.2).val) _ _ _)

-- A compound Fin.val specification also composes with ordinary arithmetic.
example := (by source_fun_prop : HasProgramInO
    (fun x : Σ n, Σ k, FinVector (Fin k) n × Fin n => (x.2.2.1.get x.2.2.2).val + 1) _ _ _)

-- Indices and subtypes are stored as their values; fields and constructors are those values.
example := (by source_fun_prop :
    HasProgramInO (fun z : {n : ℕ // n < 5} => z.1) (fun v => pure v) (fun _ => 0) (fun _ => 0))

example := (by source_fun_prop : HasProgramInO (fun z : {n : ℕ // 0 < n} => z.1 + 1) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun n : ℕ => (⟨n, n.lt_succ_self⟩ : Fin (n + 1))) (fun v => pure v)
      (fun _ => 0) (fun _ => 0))

def liftWires (x : Σ n, Σ k, FinVector (Fin k) n) : Σ n, Σ k, FinVector (Fin k) n :=
  ⟨x.1 + 1, x.2.1 + 1, .ofFn (Circuit.liftInputs x.2.2.get)⟩

private theorem encode_liftWires (x : Σ n, Σ k, FinVector (Fin k) n) :
    ⌜liftWires x⌝ₜ = ⌜(x.1 + 1, x.2.1 + 1, (x.2.2.map Fin.val).push x.2.1)⌝ₜ := by
  rcases x with ⟨n, k, v⟩
  have he : ⌜FinVector.ofFn (Circuit.liftInputs v.get)⌝ₜ = ⌜(v.map Fin.val).push k⌝ₜ := by
    rw [← encode_finVector_map_val]
    congr 1
    ext i
    cases i using Fin.lastCases <;>
      simp [Circuit.liftInputs, FinVector.get_map, FinVector.get_push]
  simp only [liftWires, Sigma.encode_mk, encode_prod, he]

-- An implementation obtained through an encoding equation is selected like any other one.
theorem hasProgramIn_liftWires : HasProgramIn liftWires hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLiftWires
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    refine (HasProgramInO.of_encode encode_liftWires (by source_fun_prop :
      HasProgramInO (fun x : Σ n, Σ k, FinVector (Fin k) n =>
        (x.1 + 1, x.2.1 + 1, (x.2.2.map Fin.val).push x.2.1)) _ _ _)).mono ?_ ?_
  all_goals dominated

-- `Circuit.liftInputs` has no implementation, so this succeeds only through the selection.
attribute [local program] hasProgramIn_liftWires in
example := (by source_fun_prop :
    HasProgramIn liftWires programLiftWires IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size))

-- The output index is computed at runtime; the continuation remains typed in the source.
example := (by source_fun_prop :
    HasProgramInO (fun input : Σ n, Circuit .booleanAlgebra (n + 1) 1 => (⟨input.1 + 1, input.2⟩ : Σ n, Circuit .booleanAlgebra n 1)) _ _ _)

def optionalReverse {α : Type*} : Option (List α) → List α
  | none => []
  | some xs => xs.reverse

def hasProgramInO_optionalReverse {α : Type*} [UniqueEncoding Tree α] :=
  (by source_fun_prop : HasProgramInO (optionalReverse (α := α)) _ _ _)

theorem optionalReverse_fdtisp {α : Type*} [UniqueEncoding Tree α] :
    optionalReverse (α := α) ∈ FDTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop

def reverseWithPrefix {α : Type*} (input : List α × Option (List α)) : List α :=
  match input.2 with
  | none => input.1
  | some xs => xs.reverse ++ input.1

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (reverseWithPrefix (α := α)) _ _ _)

def indexedReverse (input : Σ n, Option (Fin n × List Bool)) : ℕ × List Bool :=
  match input with
  | ⟨n, none⟩ => (n + 1, [])
  | ⟨_, some (i, xs)⟩ => (i.val + 1, xs.reverse)

example := (by source_fun_prop :
    HasProgramInO indexedReverse _ _ _)

attribute [local program] hasProgramInO_optionalReverse

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun x : Option (List α) => (optionalReverse x).reverse) _ _ _)

example {α : Type*} [UniqueEncoding Tree α]
    {f : List α → List α} {q : Value → Code Value} {t p : List α → ℕ} (hf : HasProgramInO f q t p) := (by source_fun_prop :
    HasProgramInO (fun input : Option (List α) => match input with | none => [] | some xs => f xs) _ _ _)

example (_f : List Bool → List Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun input : Option (List Bool) => match input with | none => [] | some xs => _f xs) _ _ _)
  trivial

-- The retained input and the reversal are both stored; both resources stay linear.
example : HasProgramInO retainsInput hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop

def nested (xs : List Bool) :=
  let ys := xs.reverse
  let zs := ys ++ xs
  zs.reverse ++ ys

example : HasProgramInO nested hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Source and output types can differ without another representation class.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] := (by source_fun_prop :
    HasProgramInO (Prod.fst : α × β → α) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun x : α => (x, x)) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xs : List α => let ys := xs.reverse; (ys, xs)) _ _ _)

def hasProgramInO_helper := (by source_fun_prop : HasProgramInO helper _ _ _)

attribute [local program] hasProgramInO_helper

-- A helper can be called only on a let-bound value, while the continuation retains its input.
def helperInLet (xs : List Bool) :=
  let ys := helper xs
  helper ys ++ xs

example := (by source_fun_prop :
    HasProgramInO helperInLet _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun xs : List Bool => let f := helper; f (f xs)) _ _ _)

-- A local implementation explicitly selects the callback.

example {q : Value → Code Value} {t p : List Bool → ℕ} (_hf : HasProgramInO helper q t p) :
    HasProgramInO (fun xs => (helper xs).reverse) (fun v => q v >>= List.Code.reverse)
      (fun xs => t xs + ⌜helper xs⌝ₜ.size) (fun xs => max (p xs) ⌜helper xs⌝ₜ.size) := by
  source_fun_prop

-- Unused lets need no implementation, including when their value is a new recursive function.
example : HasProgramInO (fun xs : List Bool => let _ys := recursive xs; xs) hole(⊢ program) (fun _ => 0)
    (fun _ => 0) := by
  fill_hole program in source_fun_prop

/-- error: source translation: `ComplexityTest.SourceTranslation.SpecComparison.recursive` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[program]`) -/
#guard_msgs in
example : HasProgramInO recursive hole(⊢ program) (fun _ => 1) (fun _ => 1) := by
  fill_hole program in source_fun_prop

@[tree_encoding]
structure Packed (α : Type*) where
  values : List α
  original : List α

@[tree_encoding]
inductive Tagged (α : Type*) where
  | one (a : α)
  | both (a b : α)
  | empty

def packedReverse {α : Type*} (xs : List α) : Packed α := ⟨xs.reverse, xs⟩

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (packedReverse : List α → Packed α) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xs : List α => some xs.reverse) _ _ _)


-- The layout equations suffice even for nested constructors: no type-specific resource rule.
example {α : Type*} [UniqueEncoding Tree α] :
    HasProgramInO (fun x : α => [Tagged.one x, Tagged.both x x]) hole(⊢ program) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- A missing opaque implementation is not silently compiled or assumed free.
opaque hidden (xs : List Bool) : List Bool := xs.reverse

example : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO hidden _ _ _)
  trivial

-- A uniform local certificate can supply even a recursive implementation.
example :
    let f := recursive
    ∀ {q : Value → Code Value} {t p : List Bool → ℕ} (_hf : HasProgramInO f q t p),
      HasProgramInO (fun xs => (f xs).reverse) (fun v => q v >>= List.Code.reverse)
        (fun xs => t xs + ⌜f xs⌝ₜ.size) (fun xs => max (p xs) ⌜f xs⌝ₜ.size) := by
  intro f q t p hf
  source_fun_prop

theorem branch_fdtisp : branch ∈ FDTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop

-- The condition is charged, and only the selected branch contributes its running time.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β} {qc qf qg : Value → Code Value} {tc pc tf pf tg pg : α → ℕ}
    (_hc : HasProgramInO c qc tc pc) (_ht : HasProgramInO f qf tf pf)
      (_hf : HasProgramInO g qg tg pg) :
    HasProgramInO (fun x => if c x then f x else g x) hole(qc, qf, qg ⊢ program)
      (fun x => (tc x + if c x then tf x else tg x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pg x))) := by
  fill_hole program in source_fun_prop

def conditionalReverse {α : Type*} (x : Bool × List α) : List α :=
  if x.1 then x.2.reverse else x.2 ++ x.2

def hasProgramInO_branch := (by source_fun_prop : HasProgramInO branch _ _ _)

attribute [local program] hasProgramInO_branch

example := (by source_fun_prop :
    HasProgramInO (List.map branch) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun xs : List Bool => if xs.isEmpty then xs else if xs.reverse.isEmpty then xs else xs.reverse) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun xs : List Bool => let ys := xs.reverse; if xs.isEmpty then ys else ys ++ xs) _ _ _)

-- A missing branch implementation is rejected even when the other branch is registered.
example (_f : List Bool → List Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun xs => if xs.isEmpty then _f xs else xs.reverse) _ _ _)
  trivial

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun x => (gateClauses (α := α) x).reverse) _ _ _)

-- Field access inside a registered call uses an automatically generated local certificate.
def emitGate
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × FinVector ℕ k × ℕ) :
    ℕ × CNF ℕ :=
  (x.2.2.2 + 1, gateClauses x)

example := (by source_fun_prop :
    HasProgramInO emitGate _ _ _)

theorem emitGate_fdtisp : emitGate ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  let S (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × FinVector ℕ k × ℕ) := ⌜x⌝ₜ.size
  have hS x : 0 < S x := Tree.size_pos _
  have hn : Dominated (fun x => ⌜x.2.2.2⌝ₜ.size) S := Dominated.of_le fun x => by
    rcases x with ⟨k, op, args, n⟩; simp only [S, Sigma.encode_mk, size_encode_prod]; omega
  have hn1 : Dominated (fun x => ⌜x.2.2.2 + 1⌝ₜ.size) S :=
    (hn.add_same (Dominated.const_of_pos _ hS)).mono_left fun x => size_encode_nat_succ_le x.2.2.2
  have hg : Dominated (fun x => ⌜gateClauses x⌝ₜ.size) S :=
    Dominated.of_le_mul _ gateClauses_size_le
  model_fun_prop
  all_goals
    simp only [pow_one, size_encode_prod,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ hS

-- The compiler uses structural equations, without a rule for each particular datatype; a
-- referenced definition is translated once and selected.
def tailOrEmpty {α : Type*} : List α → List α
  | [] => []
  | _ :: xs => xs

@[local program] theorem hasProgramIn_tailOrEmpty {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (tailOrEmpty (α := α)) hole(⊢ program) IsO(fun _ => 1)
      IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programTailOrEmpty
  fill_hole program in source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xs : List α => (tailOrEmpty xs).reverse) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (List.map (fun xs : List α => (tailOrEmpty xs).reverse)) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xs : List α => let ys := tailOrEmpty xs; (ys.reverse, xs)) _ _ _)

-- Separate implementations for each runtime index do not supply one uniform implementation.
example (f : ℕ → Bool → Bool) (program : ℕ → Value → Code Value)
    (_h : ∀ n, HasProgramInO (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : ℕ × Bool => f x.1 x.2) _ _ _)
  trivial

def optionPair {α : Type*} : Option α → Option (α × α)
  | none => none
  | some x => some (x, x)

def taggedSwap {α : Type*} : Tagged α → Tagged α
  | .empty => .empty
  | .one a => .one a
  | .both a b => .both b a

-- The same callback can need different field paths in different constructors.
def taggedReverse : Tagged (List Bool) → List Bool
  | .empty => []
  | .one xs => xs.reverse
  | .both _ ys => ys.reverse

example := (by source_fun_prop :
    HasProgramInO taggedReverse _ _ _)

def swapIf {α : Type*} (x : Bool × α × α) : α × α :=
  if x.1 then (x.2.2, x.2.1) else x.2

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (optionPair (α := α)) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (taggedSwap (α := α)) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (swapIf (α := α)) _ _ _)

-- The same callback is compiled once and used for every element.
example := (by source_fun_prop :
    HasProgramInO (List.map (fun x : Bool => (x, x))) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (List.map (gateClauses (α := α))) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (List.map (List.reverse : List α → List α)) _ _ _)

-- Each callback pays its own cost, even when the nested lengths are very uneven.
example : HasProgramInO (List.map (List.reverse : List Unit → List Unit)) hole(⊢ program)
    (fun xss => ⌜xss⌝ₜ.size) (fun xss => max ⌜xss⌝ₜ.size (max (⌜xss.map List.reverse⌝ₜ.size + 1)
      (xss.foldr (fun xs s => max ⌜xs⌝ₜ.size s) 0))) := by
  fill_hole program in
    exact List.hasProgramIn_reverse.toHasProgramInO.map.mono
      (Dominated.of_le fun xss => (size_encode_list xss).ge)
      (Dominated.refl _)

-- Only the size of the callback's result is given; no generated code appears in this proof.
theorem mapGateClauses_fdtisp {α : Type*} [UniqueEncoding Tree α] :
    List.map (gateClauses (α := α)) ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop (disch := dominated [gateClauses_size_le])

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {q : Value → Code Value} {t p : α → ℕ} (hf : HasProgramInO f q t p) := (by source_fun_prop :
    HasProgramInO (List.map f) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (List.map (List.map (List.reverse : List α → List α))) _ _ _)

-- An unregistered callback cannot be treated as a free host-language operation.
example (_f : Bool → Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (List.map _f) _ _ _)
  trivial

def foldReverse {α : Type*} (xs : List α) : List α :=
  xs.foldl (fun acc x => x :: acc) []

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (foldReverse (α := α)) _ _ _)

theorem foldReverse_fdtisp {α : Type*} [UniqueEncoding Tree α] :
    foldReverse (α := α) ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

def collectStep {α : Type*} (acc : List α) (x : α) := x :: acc

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xs : List α => xs.foldl collectStep []) _ _ _)

-- Both a registered traversal and a callback returning nil compose through the fold rule.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    HasProgramInO (fun xss : List (List α) => xss.foldl (fun acc xs => acc ++ xs) []) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun xs : List Bool => xs.foldl (fun acc x => if x then x :: acc else []) [])
      _ _ _)

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) {q : Value → Code Value} {t p : β × α → ℕ}
    (hf : HasProgramInO (Function.uncurry f) q t p) := (by source_fun_prop :
    HasProgramInO (fun x : β × List α => x.2.foldl f x.1) _ _ _)

example (_f : Bool → Bool → Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun xs : List Bool => xs.foldl _f false) _ _ _)
  trivial

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β}
    {q : Value → Code Value} {t p : ρ × α → ℕ} (hf : HasProgramInO (fun x : ρ × α => f x.1 x.2) q t p) :=
    (by source_fun_prop :
    HasProgramInO (fun x : ρ × List α => x.2.map (f x.1)) _ _ _)

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β}
    {q : Value → Code Value} {t p : ρ × β × α → ℕ} (hf : HasProgramInO (fun x : ρ × β × α => f x.1 x.2.1 x.2.2) q t p) :=
    (by source_fun_prop :
    HasProgramInO (fun x : ρ × β × List α => x.2.2.foldl (f x.1) x.2.1) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun x : List Bool × List (List Bool) => x.2.map (fun ys => x.1 ++ ys)) _ _ _)

example := (by source_fun_prop :
    HasProgramInO (fun x : Bool × List (List Bool) => x.2.map (fun ys => ys.map (fun y => if x.1 then y else x.1))) _ _ _)

-- Pointwise certificates need not give one implementation for all runtime naturals.
example {f : ℕ → Bool → Bool} {program : ℕ → Value → Code Value}
    (_hf : ∀ e, HasProgramInO (f e) (program e) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : ℕ × List Bool => x.2.map (f x.1)) _ _ _)
  trivial

example := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Fin n × List Bool => x.2.2.map (fun _ => x.2.1.val + 1)) _ _ _)

def repeatFlag (x : Bool × List Unit) : List Bool := x.2.map (fun _ => x.1)

-- The linear growth of a map whose callback returns a captured flag is settled without the
-- user. Guards the rules for list sums and mapped lists registered with `@[dominated_traversal]`.
theorem repeatFlag_fdtisp : repeatFlag ∈ FDTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop

-- Imported public exits retain the selected implementations and their callback specifications.
theorem gateClauses_fdtisp {α : Type*} [UniqueEncoding Tree α] :
    gateClauses (α := α) ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

theorem accumulateGate_fdtisp :
    accumulateGate ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

theorem circuitStep_fdtisp :
    circuitStep ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

theorem circuitContinues_fdtisp :
    circuitContinues ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

theorem circuitFinish_fdtisp :
    circuitFinish ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

theorem tseitinLoop_fdtisp :
    (fun x : TseitinState => tseitinLoop x.1 x.2) ∈
      FDTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) :=
  hasProgramIn_tseitinLoop.mem_fdtisp_pow (by decide)

end ComplexityTest.SourceTranslation.Examples
