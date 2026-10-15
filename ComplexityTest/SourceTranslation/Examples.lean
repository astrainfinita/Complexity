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

attribute [local fun_prop] duplicateImplementation

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

example : ∃ impl : Implementation sharePlain, ∀ xs, impl.bounds.time xs = 39 * xs.length + 24 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp
  omega

example : ∃ impl : Implementation unshared, ∀ xs, impl.bounds.time xs = 52 * xs.length + 32 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp
  omega

-- Local certificates also work, without exposing or naming the model implementation.
example {f : List Bool → List Bool} (hf : Implementation f) :
    ∃ impl : Implementation (fun xs => (f xs).reverse),
      ∀ xs, impl.bounds.time xs = hf.bounds.time xs + (13 * (f xs).length + 8) := by
  refine ⟨by source_fun_prop, ?_⟩
  simp

-- Eliminating an unused let is an allowed optimization: certify the identity implementation.
example : ∃ impl : Implementation (fun xs : List Bool => let _ys := xs.reverse; xs),
    ∀ xs, impl.bounds.time xs = 0 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp

-- Match existing operations instead of generating arbitrary new append expressions.
example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2)) :=
  ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun x : List α × ℕ => x.1[x.2]?)) := ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun x : Σ n, (Fin n → List Bool) × Fin n =>
    (x.2.1 x.2.2).reverse)) := ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] (n : ℕ) :
    Nonempty (Implementation (fun x : (Fin n → α) × Fin n => x.1 x.2)) := ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n =>
    (x.2.2.1 x.2.2.2).val)) := ⟨by source_fun_prop⟩

-- A compound Fin.val specification also composes with ordinary arithmetic.
example : Nonempty (Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n =>
    (x.2.2.1 x.2.2.2).val + 1)) := ⟨by source_fun_prop⟩

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

@[local fun_prop] def liftWiresImplementation : Implementation liftWires :=
  Implementation.ofEncode encode_liftWires (by source_fun_prop)

example : Implementation liftWires := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun x : Σ n, Fin n → α => List.ofFn x.2)) := ⟨by source_fun_prop⟩

example (_f : ℕ → Bool) : True := by
  fail_if_success have : Nonempty (Implementation (fun n : ℕ =>
      List.ofFn (fun i : Fin n => _f i.val))) := ⟨by source_fun_prop⟩
  trivial

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β}
    (hf : Implementation (fun x => ⌜f x⌝ₜ)) :
    Nonempty (Implementation (fun x => List.ofFn (f x))) := by
  exact ⟨by source_fun_prop⟩

-- The output index is computed at runtime; the continuation remains typed in the source.
example : Nonempty (Implementation (fun input : Σ n, Circuit .booleanAlgebra (n + 1) 1 =>
    (⟨input.1 + 1, input.2⟩ : Σ n, Circuit .booleanAlgebra n 1))) := ⟨by source_fun_prop⟩

def optionalReverse {α : Type*} : Option (List α) → List α
  | none => []
  | some xs => xs.reverse

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (optionalReverse (α := α))) := ⟨by source_fun_prop⟩

theorem optionalReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    optionalReverse (α := α) ∈ FTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop
  all_goals
    apply Dominated.of_cover (fun _ : Unit => (none : Option (List α))) some
      (by intro x; cases x <;> simp)
    all_goals
      simp only [Function.comp_def, encode_option_none, encode_option_some, size_encode_prod,
        size_encode_unit, source_bounds, Dominated.add_iff, Dominated.max_iff,
        Dominated.const_mul_left_iff, Nat.ofNat_pos]
      repeat' apply And.intro
      all_goals first
        | exact Dominated.const _
        | exact Dominated.const_of_pos _ (fun _ => by omega)
        | exact Dominated.of_le (fun xs => by have := length_le_codeSize xs; omega)

def reverseWithPrefix {α : Type*} (input : List α × Option (List α)) : List α :=
  match input.2 with
  | none => input.1
  | some xs => xs.reverse ++ input.1

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (reverseWithPrefix (α := α))) := ⟨by source_fun_prop⟩

def indexedReverse (input : Σ n, Option (Fin n × List Bool)) : ℕ × List Bool :=
  match input with
  | ⟨n, none⟩ => (n + 1, [])
  | ⟨_, some (i, xs)⟩ => (i.val + 1, xs.reverse)

example : Nonempty (Implementation indexedReverse) := ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun x : Option (List α) => (optionalReverse x).reverse)) :=
  ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α]
    {f : List α → List α} (hf : Implementation f) :
    Nonempty (Implementation (fun input : Option (List α) =>
      match input with | none => [] | some xs => f xs)) := by
  exact ⟨by source_fun_prop⟩

example (_f : List Bool → List Bool) : True := by
  fail_if_success have : Nonempty (Implementation (fun input : Option (List Bool) =>
    match input with | none => [] | some xs => _f xs)) := ⟨by source_fun_prop⟩
  trivial

example : ∃ impl : Implementation retainsInput, ∀ xs,
    impl.bounds.time xs = 39 * xs.length + 27 ∧ impl.bounds.peak xs ≤ 2 * ⌜xs⌝ₜ.size + 1 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp
  omega

def nested (xs : List Bool) :=
  let ys := xs.reverse
  let zs := ys ++ xs
  zs.reverse ++ ys

example : ∃ impl : Implementation nested, ∀ xs,
    impl.bounds.time xs = 117 * xs.length + 55 ∧ impl.bounds.peak xs ≤ 4 * ⌜xs⌝ₜ.size + 1 := by
  refine ⟨by source_fun_prop, ?_⟩
  intro xs
  have hs := size_encode_list_append xs.reverse xs
  simp_all
  omega

-- Source and output types can differ without another representation class.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    Implementation (Prod.fst : α × β → α) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : α => (x, x)) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => let ys := xs.reverse; (ys, xs)) := by source_fun_prop

-- A helper can be called only on a let-bound value, while the continuation retains its input.
def helperInLet (xs : List Bool) :=
  let ys := helper xs
  helper ys ++ xs

example : Implementation helperInLet := by source_fun_prop

example : Implementation (fun xs : List Bool => let f := helper; f (f xs)) := by source_fun_prop

-- A local implementation explicitly selects the callback.

example (hf : Implementation helper) :
    ∃ impl : Implementation (fun xs => (helper xs).reverse),
      ∀ xs, impl.bounds.time xs = hf.bounds.time xs + (13 * (helper xs).length + 8) := by
  refine ⟨by source_fun_prop, ?_⟩
  simp

-- Unused lets need no implementation, including when their value is a new recursive function.
example : ∃ impl : Implementation (fun xs : List Bool => let _ys := recursive xs; xs),
    ∀ xs, impl.bounds.time xs = 0 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp

/-- error: source translation: `ComplexityTest.SourceTranslation.SpecComparison.recursive` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`) -/
#guard_msgs in
example : Implementation recursive := by
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

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (packedReverse : List α → Packed α) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => some xs.reverse) := by source_fun_prop


-- The layout equations suffice even for nested constructors: no type-specific resource rule.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ impl : Implementation (fun x : α => [Tagged.one x, Tagged.both x x]),
      ∀ x, impl.bounds.time x = 6 ∧ impl.bounds.peak x = 3 * ⌜x⌝ₜ.size + 10 := by
  refine ⟨by source_fun_prop, ?_⟩
  intro x
  simp
  omega

-- A missing opaque implementation is not silently compiled or assumed free.
opaque hidden (xs : List Bool) : List Bool := xs.reverse

example : True := by
  fail_if_success have : Nonempty (Implementation hidden) := ⟨by source_fun_prop⟩
  trivial

-- A uniform local certificate can supply even a recursive implementation.
example :
    let f := recursive
    ∀ hf : Implementation f, ∃ impl : Implementation (fun xs => (f xs).reverse),
      ∀ xs, impl.bounds.time xs = hf.bounds.time xs + (13 * (f xs).length + 8) := by
  intro f hf
  refine ⟨by source_fun_prop, ?_⟩
  simp [f]

theorem branch_ftisp : branch ∈ FTISP .tree (fun n => n) (fun n => n) := by
  model_fun_prop
  all_goals
    apply Dominated.of_cover (fun _ : Unit => ([] : List Bool))
      (fun p : Bool × List Bool => p.1 :: p.2)
      (by intro xs; cases xs <;> simp)
    all_goals
      simp only [Function.comp_def, List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true,
        ite_true, ite_false, source_bounds, encode_bool_true, encode_bool_false,
        encode_list_nil, encode_list_cons, size_encode_prod, size_encode_unit,
        Dominated.add_iff, Dominated.max_iff]
      repeat' apply And.intro
      all_goals first
        | exact Dominated.const _
        | exact Dominated.const_of_pos _ (fun _ => by omega)
        | exact Dominated.zero
        | apply Dominated.of_le
          intro p
          have := length_le_codeSize p.2
          omega

-- The condition is charged, and only the selected branch contributes its running time.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β} (hc : Implementation c) (ht : Implementation f) (hf : Implementation g) :
    ∃ impl : Implementation (fun x => if c x then f x else g x),
      ∀ x, impl.bounds.time x = hc.bounds.time x + (if c x then ht.bounds.time x else hf.bounds.time x) + 3 := by
  refine ⟨by source_fun_prop, ?_⟩
  simp

def conditionalReverse {α : Type*} (x : Bool × List α) : List α :=
  if x.1 then x.2.reverse else x.2 ++ x.2

example : Nonempty (Implementation (List.map branch)) := ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun xs : List Bool =>
    if xs.isEmpty then xs else if xs.reverse.isEmpty then xs else xs.reverse)) :=
  ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun xs : List Bool =>
    let ys := xs.reverse; if xs.isEmpty then ys else ys ++ xs)) :=
  ⟨by source_fun_prop⟩

-- A missing branch implementation is rejected even when the other branch is registered.
example (_f : List Bool → List Bool) : True := by
  fail_if_success have : Nonempty (Implementation (fun xs => if xs.isEmpty then _f xs else xs.reverse)) :=
    ⟨by source_fun_prop⟩
  trivial

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun x => (gateClauses (α := α) x).reverse)) := by
  refine ⟨by source_fun_prop⟩

-- Field access inside a registered call uses an automatically generated local certificate.
def emitGate
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ) :
    ℕ × CNF ℕ :=
  (x.2.2.2 + 1, gateClauses x)

example : Nonempty (Implementation emitGate) := ⟨by source_fun_prop⟩

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

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun xs : List α => (tailOrEmpty xs).reverse)) :=
  ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (List.map (fun xs : List α => (tailOrEmpty xs).reverse))) :=
  ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun xs : List α => let ys := tailOrEmpty xs; (ys.reverse, xs))) :=
  ⟨by source_fun_prop⟩

-- Separate implementations for each runtime index do not supply one uniform implementation.
example (f : ℕ → Bool → Bool) (_h : ∀ n, Implementation (f n)) : True := by
  fail_if_success have : Nonempty (Implementation (fun x : ℕ × Bool => f x.1 x.2)) :=
    ⟨by source_fun_prop⟩
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

example : Nonempty (Implementation taggedReverse) := ⟨by source_fun_prop⟩

def swapIf {α : Type*} (x : Bool × α × α) : α × α :=
  if x.1 then (x.2.2, x.2.1) else x.2

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (optionPair (α := α)) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (taggedSwap (α := α)) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    Implementation (swapIf (α := α)) := by source_fun_prop

-- The same callback is compiled once and used for every element.
example : Nonempty (Implementation (List.map (fun x : Bool => (x, x)))) := by
  exact ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (List.map (gateClauses (α := α)))) := by
  exact ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (List.map (List.reverse : List α → List α))) := by
  exact ⟨by source_fun_prop⟩

-- Each callback pays its own cost, even when the nested lengths are very uneven.
example (m : ℕ) :
    (Implementation.reverse.map (α := List Unit)).bounds.time
      (List.replicate m () :: List.replicate m []) = 47 * m + 49 := by
  simp [mapBounds, reverseBounds]
  omega

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
    simp only [pow_one, Function.comp_apply, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff, Nat.ofNat_pos]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.list_foldr_max_le
      exact Dominated.of_le fun z => size_encode_le_list_of_mem z.2

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} (hf : Implementation f) :
    Nonempty (Implementation (List.map f)) := by
  exact ⟨by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (List.map (List.map (List.reverse : List α → List α)))) :=
  ⟨by source_fun_prop⟩

-- An unregistered callback cannot be treated as a free host-language operation.
example (_f : Bool → Bool) : True := by
  fail_if_success have : Nonempty (Implementation (List.map _f)) := ⟨by source_fun_prop⟩
  trivial

def foldReverse {α : Type*} (xs : List α) : List α :=
  xs.foldl (fun acc x => x :: acc) []

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (foldReverse (α := α))) := ⟨by source_fun_prop⟩

theorem foldReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    foldReverse (α := α) ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  have h := prependFold_growth (α := α)
  let initial : Implementation (fun xs : List α => (([] : List α), xs)) := by source_fun_prop
  have initial_growth : initial.HasGrowth (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
    source_fun_prop
    · exact Dominated.const _
    · simp only [size_encode_prod, encode_list_nil, Dominated.max_iff, Dominated.add_iff]
      repeat' apply And.intro
      all_goals first
        | exact Dominated.refl _
        | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
  apply ((initial_growth.comp h).mono ?_ ?_).mem_ftisp_pow (by decide : 0 < 1)
  · simp only [pow_one, Dominated.add_iff]
    exact ⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨Dominated.of_le length_le_codeSize, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩⟩
  · simp only [pow_one, size_encode_prod, encode_list_nil,
      Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

def collectStep {α : Type*} (acc : List α) (x : α) := x :: acc

example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun xs : List α => xs.foldl collectStep [])) := ⟨by source_fun_prop⟩

-- Both a registered traversal and a callback returning nil compose through the fold rule.
example {α : Type*} [UniqueEncoding Tree α] :
    Nonempty (Implementation (fun xss : List (List α) => xss.foldl (fun acc xs => acc ++ xs) [])) :=
  ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun xs : List Bool =>
    xs.foldl (fun acc x => if x then x :: acc else []) [])) := ⟨by source_fun_prop⟩

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (hf : Implementation (Function.uncurry f)) :
    Nonempty (Implementation (fun x : β × List α => x.2.foldl f x.1)) := by
  exact ⟨by source_fun_prop⟩

example (_f : Bool → Bool → Bool) : True := by
  fail_if_success have : Nonempty (Implementation (fun xs : List Bool => xs.foldl _f false)) :=
    ⟨by source_fun_prop⟩
  trivial

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β}
    (hf : Implementation (fun x : ρ × α => f x.1 x.2)) :
    Nonempty (Implementation (fun x : ρ × List α => x.2.map (f x.1))) := by
  exact ⟨by source_fun_prop⟩

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β}
    (hf : Implementation (fun x : ρ × β × α => f x.1 x.2.1 x.2.2)) :
    Nonempty (Implementation (fun x : ρ × β × List α => x.2.2.foldl (f x.1) x.2.1)) := by
  exact ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun x : List Bool × List (List Bool) =>
    x.2.map (fun ys => x.1 ++ ys))) := ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun x : Bool × List (List Bool) =>
    x.2.map (fun ys => ys.map (fun y => if x.1 then y else x.1)))) :=
  ⟨by source_fun_prop⟩

-- Pointwise certificates need not give one implementation for all runtime naturals.
example {f : ℕ → Bool → Bool}
    (_hf : ∀ e, Implementation (f e)) : True := by
  fail_if_success have : Nonempty (Implementation (fun x : ℕ × List Bool => x.2.map (f x.1))) :=
    ⟨by source_fun_prop⟩
  trivial

example : Nonempty (Implementation (fun x : Σ n, Fin n × List Bool =>
    x.2.2.map (fun _ => x.2.1.val + 1))) := ⟨by source_fun_prop⟩

def repeatFlag (x : Bool × List Unit) : List Bool := x.2.map (fun _ => x.1)

theorem repeatFlag_ftisp : repeatFlag ∈ FTISP .tree (fun n => n) (fun n => n) := by
  have hs : Dominated (fun x : Bool × List Unit => ⌜x.2⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    Dominated.of_le size_encode_snd_le
  have hl : Dominated (fun x : Bool × List Unit => x.2.length) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.of_le (fun x : Bool × List Unit => length_le_codeSize x.2)).trans hs
  have hout : Dominated (fun x : Bool × List Unit => ⌜List.replicate x.2.length x.1⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.trans (Dominated.of_le_mul 3 ?_) hs
    intro x
    simpa only [List.map_const'] using size_encode_map_le (fun _ : Unit => x.1) x.2 3
      (by decide) (fun a _ => by cases a; simpa using size_encode_bool_le x.1)
  have hu (u : Unit) : ⌜u⌝ₜ.size = 1 := by cases u; rfl
  model_fun_prop
  all_goals
    simp only [source_bounds, size_encode_prod,
      List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.reduceAdd, ← Nat.max_assoc,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals first
    | assumption
    | simpa only [Nat.mul_comm] using hl.const_mul_left 2
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.foldr_max_le
      simp only [hu, Dominated.max_iff, Dominated.add_iff]
      repeat' apply And.intro
      all_goals first
        | exact Dominated.refl _
        | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

-- Imported public exits retain the selected implementations and their callback specifications.
theorem accumulateGate_ftisp :
    accumulateGate ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals simp only [pow_zero, pow_one]
  all_goals exact Dominated.refl _

theorem circuitStep_ftisp :
    circuitStep ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    apply Dominated.of_le
    rintro ⟨input, acc⟩
    simp only [pow_one, size_encode_prod]
    omega

end ComplexityTest.SourceTranslation.Examples
