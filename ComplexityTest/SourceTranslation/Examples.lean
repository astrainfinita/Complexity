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

open ComplexityTest.SourceTranslation.SpecComparison

namespace ComplexityTest.SourceTranslation.Examples

attribute [local fun_prop] implementationDuplicate

private theorem size_encode_map_le {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] (f : α → β) (xs : List α)
    (k : ℕ) (hk : 1 ≤ k) (h : ∀ x ∈ xs, ⌜f x⌝ₜ.size ≤ k * ⌜x⌝ₜ.size) :
    ⌜xs.map f⌝ₜ.size ≤ k * ⌜xs⌝ₜ.size := by
  induction xs with
  | nil => simpa using hk
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have := ih h.2
    simp only [List.map_cons, encode_list_cons, size_encode_prod]
    nlinarith [h.1]

-- A shared let computes the reversal once; the unshared source reverses twice.
example : Implementation sharePlain (fun xs => ⌜xs⌝ₜ.size + (0 + (0 + (xs.reverse.length + 1))))
    (fun xs => max ⌜xs⌝ₜ.size (max 0 (max 0 (⌜xs.reverse⌝ₜ.size + ⌜xs.reverse⌝ₜ.size)))) := by
  source_fun_prop

example : Implementation unshared
    (fun xs => ⌜xs⌝ₜ.size + (⌜xs⌝ₜ.size + (xs.reverse.length + 1)))
    (fun xs => max ⌜xs⌝ₜ.size (max ⌜xs⌝ₜ.size (⌜xs.reverse⌝ₜ.size + ⌜xs.reverse⌝ₜ.size))) := by
  source_fun_prop

-- Local implementations also work, without exposing or naming the model implementation.
example {f : List Bool → List Bool} {t p : List Bool → ℕ} (_hf : Implementation f t p) :
    Implementation (fun xs => (f xs).reverse) (fun xs => t xs + ⌜f xs⌝ₜ.size)
      (fun xs => max (p xs) ⌜f xs⌝ₜ.size) := by
  source_fun_prop

-- Eliminating an unused let is an allowed optimization: certify the identity implementation.
example : Implementation (fun xs : List Bool => let _ys := xs.reverse; xs) (fun _ => 0)
    (fun _ => 0) := by
  source_fun_prop

-- Match existing operations instead of generating arbitrary new append expressions.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x : List α × ℕ => x.1[x.2]?) _ _)

example := (by source_fun_prop :
    Implementation (fun x : Σ n, (Fin n → List Bool) × Fin n => (x.2.1 x.2.2).reverse) _ _)

example {α : Type*} [UniqueEncoding Tree α] (n : ℕ) := (by source_fun_prop :
    Implementation (fun x : (Fin n → α) × Fin n => x.1 x.2) _ _)

example := (by source_fun_prop :
    Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n => (x.2.2.1 x.2.2.2).val) _ _)

-- A compound Fin.val specification also composes with ordinary arithmetic.
example := (by source_fun_prop :
    Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n => (x.2.2.1 x.2.2.2).val + 1) _ _)

def liftWires (x : Σ n, Σ k, Fin n → Fin k) : Σ n, Σ k, Fin n → Fin k :=
  ⟨x.1 + 1, x.2.1 + 1, Circuit.liftInputs x.2.2⟩

private theorem encode_liftWires (x : Σ n, Σ k, Fin n → Fin k) :
    ⌜liftWires x⌝ₜ = ⌜(x.1 + 1, x.2.1 + 1, List.ofFn (Fin.val ∘ x.2.2) ++ [x.2.1])⌝ₜ := by
  rcases x with ⟨n, k, f⟩
  have he : ⌜Circuit.liftInputs f⌝ₜ = ⌜List.ofFn (Fin.val ∘ f) ++ [k]⌝ₜ := by
    rw [encode_fin_function, ← encode_fin_values (Circuit.liftInputs f)]
    simp only [Circuit.liftInputs, Fin.comp_snoc]
    rw [List.ofFn_succ']
    simp [Function.comp_def]
  simp only [liftWires, Sigma.encode_mk, encode_prod, he]

def implementationLiftWires := Implementation.ofEncode encode_liftWires (by source_fun_prop :
  Implementation (fun x : Σ n, Σ k, Fin n → Fin k =>
    (x.1 + 1, x.2.1 + 1, List.ofFn (Fin.val ∘ x.2.2) ++ [x.2.1])) _ _)

attribute [local fun_prop] implementationLiftWires

example : (by source_fun_prop : Implementation liftWires _ _).program =
    implementationLiftWires.program := rfl

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2) _ _)

example (_f : ℕ → Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun n : ℕ => List.ofFn (fun i : Fin n => _f i.val)) _ _)
  trivial

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β}
    {t p : α → ℕ} (hf : Implementation (fun x => ⌜f x⌝ₜ) t p) := (by source_fun_prop :
    Implementation (fun x => List.ofFn (f x)) _ _)

-- The output index is computed at runtime; the continuation remains typed in the source.
example := (by source_fun_prop :
    Implementation (fun input : Σ n, Circuit .booleanAlgebra (n + 1) 1 => (⟨input.1 + 1, input.2⟩ : Σ n, Circuit .booleanAlgebra n 1)) _ _)

def optionalReverse {α : Type*} : Option (List α) → List α
  | none => []
  | some xs => xs.reverse

def implementationOptionalReverse {α : Type*} [UniqueEncoding Tree α] :=
  (by source_fun_prop : Implementation (optionalReverse (α := α)) _ _)

theorem optionalReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    optionalReverse (α := α) ∈ FTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop
  all_goals dominated

def reverseWithPrefix {α : Type*} (input : List α × Option (List α)) : List α :=
  match input.2 with
  | none => input.1
  | some xs => xs.reverse ++ input.1

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (reverseWithPrefix (α := α)) _ _)

def indexedReverse (input : Σ n, Option (Fin n × List Bool)) : ℕ × List Bool :=
  match input with
  | ⟨n, none⟩ => (n + 1, [])
  | ⟨_, some (i, xs)⟩ => (i.val + 1, xs.reverse)

example := (by source_fun_prop :
    Implementation indexedReverse _ _)

attribute [local source] implementationOptionalReverse

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x : Option (List α) => (optionalReverse x).reverse) _ _)

example {α : Type*} [UniqueEncoding Tree α]
    {f : List α → List α} {t p : List α → ℕ} (hf : Implementation f t p) := (by source_fun_prop :
    Implementation (fun input : Option (List α) => match input with | none => [] | some xs => f xs) _ _)

example (_f : List Bool → List Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun input : Option (List Bool) => match input with | none => [] | some xs => _f xs) _ _)
  trivial

-- The retained input and the reversal are both stored; both resources stay linear.
example : Implementation retainsInput (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def nested (xs : List Bool) :=
  let ys := xs.reverse
  let zs := ys ++ xs
  zs.reverse ++ ys

example : Implementation nested (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

-- Source and output types can differ without another representation class.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] := (by source_fun_prop :
    Implementation (Prod.fst : α × β → α) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x : α => (x, x)) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xs : List α => let ys := xs.reverse; (ys, xs)) _ _)

def implementationHelper := (by source_fun_prop : Implementation helper _ _)

attribute [local source] implementationHelper

-- A helper can be called only on a let-bound value, while the continuation retains its input.
def helperInLet (xs : List Bool) :=
  let ys := helper xs
  helper ys ++ xs

example := (by source_fun_prop :
    Implementation helperInLet _ _)

example := (by source_fun_prop :
    Implementation (fun xs : List Bool => let f := helper; f (f xs)) _ _)

-- A local implementation explicitly selects the callback.

example {t p : List Bool → ℕ} (_hf : Implementation helper t p) :
    Implementation (fun xs => (helper xs).reverse) (fun xs => t xs + ⌜helper xs⌝ₜ.size)
      (fun xs => max (p xs) ⌜helper xs⌝ₜ.size) := by
  source_fun_prop

-- Unused lets need no implementation, including when their value is a new recursive function.
example : Implementation (fun xs : List Bool => let _ys := recursive xs; xs) (fun _ => 0)
    (fun _ => 0) := by
  source_fun_prop

/-- error: source translation: `ComplexityTest.SourceTranslation.SpecComparison.recursive` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`) -/
#guard_msgs in
example : Implementation recursive (fun _ => 1) (fun _ => 1) := by
  source_fun_prop

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
    Implementation (packedReverse : List α → Packed α) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xs : List α => some xs.reverse) _ _)


-- The layout equations suffice even for nested constructors: no type-specific resource rule.
example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : α => [Tagged.one x, Tagged.both x x]) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

-- A missing opaque implementation is not silently compiled or assumed free.
opaque hidden (xs : List Bool) : List Bool := xs.reverse

example : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation hidden _ _)
  trivial

-- A uniform local certificate can supply even a recursive implementation.
example :
    let f := recursive
    ∀ {t p : List Bool → ℕ} (_hf : Implementation f t p),
      Implementation (fun xs => (f xs).reverse) (fun xs => t xs + ⌜f xs⌝ₜ.size)
        (fun xs => max (p xs) ⌜f xs⌝ₜ.size) := by
  intro f t p hf
  source_fun_prop

theorem branch_ftisp : branch ∈ FTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop
  all_goals dominated

-- The condition is charged, and only the selected branch contributes its running time.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β} {tc pc tf pf tg pg : α → ℕ} (_hc : Implementation c tc pc)
    (_ht : Implementation f tf pf) (_hf : Implementation g tg pg) :
    Implementation (fun x => if c x then f x else g x)
      (fun x => (tc x + if c x then tf x else tg x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pg x))) := by
  source_fun_prop

def conditionalReverse {α : Type*} (x : Bool × List α) : List α :=
  if x.1 then x.2.reverse else x.2 ++ x.2

def implementationBranch := (by source_fun_prop : Implementation branch _ _)

attribute [local source] implementationBranch

example := (by source_fun_prop :
    Implementation (List.map branch) _ _)

example := (by source_fun_prop :
    Implementation (fun xs : List Bool => if xs.isEmpty then xs else if xs.reverse.isEmpty then xs else xs.reverse) _ _)

example := (by source_fun_prop :
    Implementation (fun xs : List Bool => let ys := xs.reverse; if xs.isEmpty then ys else ys ++ xs) _ _)

-- A missing branch implementation is rejected even when the other branch is registered.
example (_f : List Bool → List Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun xs => if xs.isEmpty then _f xs else xs.reverse) _ _)
  trivial

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun x => (gateClauses (α := α) x).reverse) _ _)

-- Field access inside a registered call uses an automatically generated local certificate.
def emitGate
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ) :
    ℕ × CNF ℕ :=
  (x.2.2.2 + 1, gateClauses x)

example := (by source_fun_prop :
    Implementation emitGate _ _)

theorem emitGate_ftisp : emitGate ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  let S (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ) := ⌜x⌝ₜ.size
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

-- The compiler uses structural equations, without a rule for each particular datatype.
def tailOrEmpty {α : Type*} : List α → List α
  | [] => []
  | _ :: xs => xs

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xs : List α => (tailOrEmpty xs).reverse) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (List.map (fun xs : List α => (tailOrEmpty xs).reverse)) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xs : List α => let ys := tailOrEmpty xs; (ys.reverse, xs)) _ _)

-- Separate implementations for each runtime index do not supply one uniform implementation.
example (f : ℕ → Bool → Bool) (_h : ∀ n, Implementation (f n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun x : ℕ × Bool => f x.1 x.2) _ _)
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
    Implementation taggedReverse _ _)

def swapIf {α : Type*} (x : Bool × α × α) : α × α :=
  if x.1 then (x.2.2, x.2.1) else x.2

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (optionPair (α := α)) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (taggedSwap (α := α)) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (swapIf (α := α)) _ _)

-- The same callback is compiled once and used for every element.
example := (by source_fun_prop :
    Implementation (List.map (fun x : Bool => (x, x))) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (List.map (gateClauses (α := α))) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (List.map (List.reverse : List α → List α)) _ _)

-- Each callback pays its own cost, even when the nested lengths are very uneven.
example : Implementation (List.map (List.reverse : List Unit → List Unit))
    (fun xss => ⌜xss⌝ₜ.size) (fun xss => max ⌜xss⌝ₜ.size (max (⌜xss.map List.reverse⌝ₜ.size + 1)
      (xss.foldr (fun xs s => max ⌜xs⌝ₜ.size s) 0))) :=
  List.implementationReverse.map.mono (Dominated.of_le fun xss => (size_encode_list xss).ge)
    (Dominated.refl _)

-- Only ordinary size arithmetic remains; no generated code appears in this proof.
theorem mapGateClauses_ftisp {α : Type*} [UniqueEncoding Tree α] :
    List.map (gateClauses (α := α)) ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  have hout := Dominated.of_le_mul 4 (fun xs =>
    size_encode_map_le (gateClauses (α := α)) xs 4 (by decide)
      (fun x _ => gateClauses_size_le x))
  have hlength := Dominated.of_le
    (length_le_codeSize : ∀ xs : List (Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
      (Fin k → α) × α), xs.length ≤ ⌜xs⌝ₜ.size)
  model_fun_prop
  all_goals
    simp only [pow_one, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.list_foldr_max_le
      exact Dominated.of_le fun z => size_encode_le_list_of_mem z.2

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {t p : α → ℕ} (hf : Implementation f t p) := (by source_fun_prop :
    Implementation (List.map f) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (List.map (List.map (List.reverse : List α → List α))) _ _)

-- An unregistered callback cannot be treated as a free host-language operation.
example (_f : Bool → Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (List.map _f) _ _)
  trivial

def foldReverse {α : Type*} (xs : List α) : List α :=
  xs.foldl (fun acc x => x :: acc) []

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (foldReverse (α := α)) _ _)

theorem foldReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    foldReverse (α := α) ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

def collectStep {α : Type*} (acc : List α) (x : α) := x :: acc

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xs : List α => xs.foldl collectStep []) _ _)

-- Both a registered traversal and a callback returning nil compose through the fold rule.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
    Implementation (fun xss : List (List α) => xss.foldl (fun acc xs => acc ++ xs) []) _ _)

example := (by source_fun_prop :
    Implementation (fun xs : List Bool => xs.foldl (fun acc x => if x then x :: acc else []) []) _ _)

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) {t p : β × α → ℕ}
    (hf : Implementation (Function.uncurry f) t p) := (by source_fun_prop :
    Implementation (fun x : β × List α => x.2.foldl f x.1) _ _)

example (_f : Bool → Bool → Bool) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun xs : List Bool => xs.foldl _f false) _ _)
  trivial

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β}
    {t p : ρ × α → ℕ} (hf : Implementation (fun x : ρ × α => f x.1 x.2) t p) :=
    (by source_fun_prop :
    Implementation (fun x : ρ × List α => x.2.map (f x.1)) _ _)

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β}
    {t p : ρ × β × α → ℕ} (hf : Implementation (fun x : ρ × β × α => f x.1 x.2.1 x.2.2) t p) :=
    (by source_fun_prop :
    Implementation (fun x : ρ × β × List α => x.2.2.foldl (f x.1) x.2.1) _ _)

example := (by source_fun_prop :
    Implementation (fun x : List Bool × List (List Bool) => x.2.map (fun ys => x.1 ++ ys)) _ _)

example := (by source_fun_prop :
    Implementation (fun x : Bool × List (List Bool) => x.2.map (fun ys => ys.map (fun y => if x.1 then y else x.1))) _ _)

-- Pointwise certificates need not give one implementation for all runtime naturals.
example {f : ℕ → Bool → Bool}
    (_hf : ∀ e, Implementation (f e) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success have := (by source_fun_prop :
    Implementation (fun x : ℕ × List Bool => x.2.map (f x.1)) _ _)
  trivial

example := (by source_fun_prop :
    Implementation (fun x : Σ n, Fin n × List Bool => x.2.2.map (fun _ => x.2.1.val + 1)) _ _)

def repeatFlag (x : Bool × List Unit) : List Bool := x.2.map (fun _ => x.1)

theorem repeatFlag_ftisp : repeatFlag ∈ FTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop
  · apply Dominated.of_le_mul 8
    rintro ⟨b, xs⟩
    have := length_le_codeSize xs
    have := Tree.size_pos ⌜xs⌝ₜ
    simp [size_encode_prod]
    omega
  · have hs : Dominated (fun x : Bool × List Unit => ⌜x.2⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le size_encode_snd_le
    have hout : Dominated (fun x : Bool × List Unit => ⌜x.2.map (fun _ => x.1)⌝ₜ.size)
        (fun x => ⌜x⌝ₜ.size) :=
      (Dominated.of_le_mul 3 fun (x : Bool × List Unit) =>
        size_encode_map_le (fun _ : Unit => x.1) x.2 3 (by decide)
        (fun a _ => by cases a; simpa using size_encode_bool_le x.1)).trans hs
    have hu (u : Unit) : ⌜u⌝ₜ.size = 1 := by cases u; rfl
    simp only [size_encode_prod, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | assumption
      | exact Dominated.refl _
      | exact Dominated.zero
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
      | apply Dominated.foldr_max_le
        apply Dominated.of_le_mul 3
        intro z
        have := Tree.size_pos ⌜z.1⌝ₜ
        simp [hu]
        omega

-- Imported public exits retain the selected implementations and their callback specifications.
theorem accumulateGate_ftisp :
    accumulateGate ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

theorem circuitStep_ftisp :
    circuitStep ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

end ComplexityTest.SourceTranslation.Examples
