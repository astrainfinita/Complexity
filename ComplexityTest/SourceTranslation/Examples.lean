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

attribute [local fun_prop] duplicate_realizes

@[local fun_prop, source_bounds↓] private noncomputable def duplicateImplementation
    {α : Type*} [UniqueEncoding Tree α] : Implementation (duplicate : List α → List α) :=
  duplicate_realizes.implementation

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

example : ∃ b, Realizes sharePlain b ∧ ∀ xs, b.time xs = 39 * xs.length + 24 := by
  refine ⟨_, by fun_prop [sharePlain], ?_⟩
  simp
  omega

example : ∃ b, Realizes unshared b ∧ ∀ xs, b.time xs = 52 * xs.length + 32 := by
  refine ⟨_, by fun_prop [unshared], ?_⟩
  simp
  omega

-- Local certificates also work, without exposing or naming the model implementation.
example {f : List Bool → List Bool} {b : Bounds (List Bool)} (hf : Realizes f b) :
    ∃ c, Realizes (fun xs => (f xs).reverse) c ∧
      ∀ xs, c.time xs = b.time xs + (13 * (f xs).length + 8) := by
  refine ⟨_, by fun_prop, ?_⟩
  simp

-- Eliminating an unused let is an allowed optimization: certify the identity implementation.
example : ∃ b, Realizes (fun xs : List Bool => let _ys := xs.reverse; xs) b ∧
    ∀ xs, b.time xs = 0 := by
  refine ⟨_, by fun_prop, ?_⟩
  simp

-- Match existing operations instead of generating arbitrary new append expressions.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) b :=
  ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : List α × ℕ => x.1[x.2]?) b := ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun x : Σ n, (Fin n → List Bool) × Fin n =>
    (x.2.1 x.2.2).reverse) b := ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] (n : ℕ) :
    ∃ b, Realizes (fun x : (Fin n → α) × Fin n => x.1 x.2) b := ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n =>
    (x.2.2.1 x.2.2.2).val) b := ⟨_, by source_fun_prop⟩

-- A compound Fin.val specification also composes with ordinary arithmetic.
example : ∃ b, Realizes (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n =>
    (x.2.2.1 x.2.2.2).val + 1) b := ⟨_, by source_fun_prop⟩

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

@[local fun_prop] theorem liftWires_realizes :
    Realizes liftWires ⟨fun x => 100 * ⌜x⌝ₜ.size + 100, fun x => 10 * ⌜x⌝ₜ.size + 10⟩ := by
  refine (Realizes.of_encode encode_liftWires (by source_fun_prop)).mono ?_
  rintro ⟨n, k, f⟩
  have hn := length_le_codeSize n.bits
  have hk := length_le_codeSize k.bits
  have hf := length_le_codeSize (List.ofFn (Fin.val ∘ f))
  have hs := size_encode_list_append (List.ofFn (Fin.val ∘ f)) [k]
  have hn' := size_encode_nat_succ_le n
  have hk' := size_encode_nat_succ_le k
  simp at *
  (repeat' apply And.intro) <;> omega

example : ∃ b, Realizes liftWires b := ⟨_, by source_fun_prop⟩

theorem liftWires_ftisp : liftWires ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := liftWires_realizes.computableInTimeAndSpace
    (time := fun n => 100 * n + 104) (space := fun n => 10 * n + 12)
    (by intro x; simp; omega)
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨204, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨22 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : Σ n, Fin n → α => List.ofFn x.2) b := ⟨_, by source_fun_prop⟩

example (_f : ℕ → Bool) : True := by
  fail_if_success have : ∃ b, Realizes (fun n : ℕ =>
      List.ofFn (fun i : Fin n => _f i.val)) b := ⟨_, by source_fun_prop⟩
  trivial

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β} {b : Bounds α}
    (hf : Realizes (fun x => ⌜f x⌝ₜ) b) :
    ∃ c, Realizes (fun x => List.ofFn (f x)) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

-- The output index is computed at runtime; the continuation remains typed in the source.
example : ∃ b, Realizes (fun input : Σ n, Circuit .booleanAlgebra (n + 1) 1 =>
    (⟨input.1 + 1, input.2⟩ : Σ n, Circuit .booleanAlgebra n 1)) b := ⟨_, by source_fun_prop⟩

def optionalReverse {α : Type*} : Option (List α) → List α
  | none => []
  | some xs => xs.reverse

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (optionalReverse (α := α)) b := ⟨_, by source_fun_prop⟩

theorem optionalReverse_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (optionalReverse (α := α))
      (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

theorem optionalReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    optionalReverse (α := α) ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := optionalReverse_model (α := α)
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨33, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨4 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

def reverseWithPrefix {α : Type*} (input : List α × Option (List α)) : List α :=
  match input.2 with
  | none => input.1
  | some xs => xs.reverse ++ input.1

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (reverseWithPrefix (α := α)) b := ⟨_, by source_fun_prop⟩

def indexedReverse (input : Σ n, Option (Fin n × List Bool)) : ℕ × List Bool :=
  match input with
  | ⟨n, none⟩ => (n + 1, [])
  | ⟨_, some (i, xs)⟩ => (i.val + 1, xs.reverse)

example : ∃ b, Realizes indexedReverse b := ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : Option (List α) => (optionalReverse x).reverse) b :=
  ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α]
    {f : List α → List α} {b : Bounds (List α)} (hf : Realizes f b) :
    ∃ c, Realizes (fun input : Option (List α) =>
      match input with | none => [] | some xs => f xs) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

example (_f : List Bool → List Bool) : True := by
  fail_if_success have : ∃ b, Realizes (fun input : Option (List Bool) =>
    match input with | none => [] | some xs => _f xs) b := ⟨_, by source_fun_prop⟩
  trivial

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace twiceLet
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace share
    (fun n => 39 * n + 28) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

theorem shared_model_bound : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace sharePlain
    (fun n => 39 * n + 28) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

theorem unshared_model_bound : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace unshared
    (fun n => 52 * n + 36) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace throughHelper
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

example (time : ℕ → ℕ) (ht : ∀ n, 39 * n + 28 ≤ time n) :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace sharePlain time
      (fun n => k * (2 * n + 3)) := by
  model_fun_prop

/--
error: unsolved goals
case hb.left
time : ℕ → ℕ
xs✝ : List Bool
⊢ 13 * xs✝.length + 8 + (26 * xs✝.length + 16) + 4 ≤ time (encode Complexity.Tree xs✝).size
-/
#guard_msgs in
example (time : ℕ → ℕ) :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace sharePlain time
      (fun n => k * (2 * n + 3)) := by
  model_fun_prop

example : ∃ b, Realizes retainsInput b ∧ ∀ xs,
    b.time xs = 39 * xs.length + 27 ∧ b.peak xs ≤ 2 * ⌜xs⌝ₜ.size + 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp
  omega

theorem retained_model_bound : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace retainsInput
    (fun n => 39 * n + 31) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

def nested (xs : List Bool) :=
  let ys := xs.reverse
  let zs := ys ++ xs
  zs.reverse ++ ys

example : ∃ b, Realizes nested b ∧ ∀ xs,
    b.time xs = 117 * xs.length + 55 ∧ b.peak xs ≤ 4 * ⌜xs⌝ₜ.size + 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro xs
  have hs := size_encode_list_append xs.reverse xs
  simp_all
  omega

theorem nested_model_bound : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace nested
    (fun n => 117 * n + 59) (fun n => k * (4 * n + 3)) := by
  model_fun_prop

-- Both the source types and the output types can differ, without a new representation class.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (Prod.fst : α × β → α)
      (fun _ => 5) (fun n => k * (n + 2)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (fun x : α => (x, x))
      (fun _ => 5) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun xs : List α => let ys := xs.reverse; (ys, xs))
      (fun n => 13 * n + 16) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

-- A helper can be called only on a let-bound value, while the continuation retains its input.
def helperInLet (xs : List Bool) :=
  let ys := helper xs
  helper ys ++ xs

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace helperInLet
    (fun n => 52 * n + 39) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

-- A local function is inlined, while a local certificate can select an existing implementation.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun xs : List Bool => let f := helper; f (f xs))
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

example (b : Bounds (List Bool)) (hf : Realizes helper b) :
    ∃ c, Realizes (fun xs => (helper xs).reverse) c ∧
      ∀ xs, c.time xs = b.time xs + (13 * (helper xs).length + 8) := by
  let callback := hf.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

-- Unused lets need no implementation, including when their value is a new recursive function.
example : ∃ b, Realizes (fun xs : List Bool => let _ys := recursive xs; xs) b ∧
    ∀ xs, b.time xs = 0 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

/-- error: source translation: `ComplexityTest.SourceTranslation.SpecComparison.recursive` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`) -/
#guard_msgs in
example : Realizes recursive identityBounds := by
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

theorem packedReverse_bound {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (packedReverse : List α → Packed α)
      (fun n => 13 * n + 13) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun xs : List α => some xs.reverse)
      (fun n => 13 * n + 13) (fun n => k * (n + 4)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (fun x : α => Tagged.both x x)
      (fun _ => 7) (fun n => k * (2 * n + 7)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun x : α => [Tagged.one x, Tagged.both x x])
      (fun _ => 10) (fun n => k * (3 * n + 12)) := by
  model_fun_prop

-- The layout equations suffice even for nested constructors: no type-specific resource rule.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : α => [Tagged.one x, Tagged.both x x]) b ∧
      ∀ x, b.time x = 6 ∧ b.peak x = 3 * ⌜x⌝ₜ.size + 10 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  simp
  omega

-- A missing opaque implementation is not silently compiled or assumed free.
opaque hidden (xs : List Bool) : List Bool := xs.reverse

example : True := by
  fail_if_success have : ∃ b, Realizes hidden b := ⟨_, by source_fun_prop⟩
  trivial

-- A uniform local certificate can supply even a recursive implementation.
example (b : Bounds (List Bool)) :
    let f := recursive
    Realizes f b → ∃ c, Realizes (fun xs => (f xs).reverse) c ∧
      ∀ xs, c.time xs = b.time xs + (13 * (f xs).length + 8) := by
  intro f hf
  let callback := hf.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  simp [f]

theorem branch_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace branch
    (fun n => 13 * n + 20) (fun n => k * (n + 4)) := by
  model_fun_prop

theorem branch_ftisp : branch ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := branch_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨33, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨5 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

-- The condition is charged, and only the selected branch contributes its running time.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β} {bc bt bf : Bounds α}
    (hc : Realizes c bc) (ht : Realizes f bt) (hf : Realizes g bf) :
    ∃ b, Realizes (fun x => if c x then f x else g x) b ∧
      ∀ x, b.time x = bc.time x + (if c x then bt.time x else bf.time x) + 3 := by
  let test := hc.implementation
  let yes := ht.implementation
  let no := hf.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

def conditionalReverse {α : Type*} (x : Bool × List α) : List α :=
  if x.1 then x.2.reverse else x.2 ++ x.2

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (conditionalReverse (α := α))
      (fun n => 26 * n + 30) (fun n => k * (2 * n + 4)) := by
  model_fun_prop

example : ∃ b, Realizes (List.map branch) b := ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun xs : List Bool =>
    if xs.isEmpty then xs else if xs.reverse.isEmpty then xs else xs.reverse) b :=
  ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun xs : List Bool =>
    let ys := xs.reverse; if xs.isEmpty then ys else ys ++ xs) b :=
  ⟨_, by source_fun_prop⟩

-- A missing branch implementation is rejected even when the other branch is registered.
example (_f : List Bool → List Bool) : True := by
  fail_if_success have : ∃ b, Realizes (fun xs => if xs.isEmpty then _f xs else xs.reverse) b :=
    ⟨_, by source_fun_prop⟩
  trivial

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x => (gateClauses (α := α) x).reverse) b := by
  refine ⟨_, by source_fun_prop⟩

-- Field access inside a registered call uses an automatically generated local certificate.
def emitGate
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ) :
    ℕ × CNF ℕ :=
  (x.2.2.2 + 1, gateClauses x)

example : ∃ b, Realizes emitGate b := ⟨_, by source_fun_prop⟩

theorem emitGate_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace emitGate
    (fun n => 28 * n + 100) (fun n => k * (6 * n + 10)) := by
  model_fun_prop
  all_goals
    rename_i x
    have hbits := length_le_codeSize x.2.2.2.bits
    have hgate := gateClauses_size_le x
    have hsucc := size_encode_nat_succ_le x.2.2.2
    rcases x with ⟨k, op, args, n⟩
    simp at *
    omega

theorem emitGate_ftisp : emitGate ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := emitGate_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨128, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨16 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

-- The compiler uses structural equations, without a rule for each particular datatype.
def tailOrEmpty {α : Type*} : List α → List α
  | [] => []
  | _ :: xs => xs

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun xs : List α => (tailOrEmpty xs).reverse) b :=
  ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (List.map (fun xs : List α => (tailOrEmpty xs).reverse)) b :=
  ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun xs : List α => let ys := tailOrEmpty xs; (ys.reverse, xs)) b :=
  ⟨_, by source_fun_prop⟩

-- Separate implementations for each runtime index do not supply one uniform implementation.
example (f : ℕ → Bool → Bool) (b : ℕ → Bounds Bool) (_h : ∀ n, Realizes (f n) (b n)) : True := by
  fail_if_success have : ∃ c, Realizes (fun x : ℕ × Bool => f x.1 x.2) c :=
    ⟨_, by source_fun_prop⟩
  trivial

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (tailOrEmpty (α := α))
      (fun _ => 6) (fun n => k * (n + 2)) := by
  model_fun_prop

def optionPair {α : Type*} : Option α → Option (α × α)
  | none => none
  | some x => some (x, x)

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (optionPair (α := α))
      (fun _ => 9) (fun n => k * (2 * n + 2)) := by
  model_fun_prop

def taggedSwap {α : Type*} : Tagged α → Tagged α
  | .empty => .empty
  | .one a => .one a
  | .both a b => .both b a

-- The same callback can need different field paths in different constructors.
def taggedReverse : Tagged (List Bool) → List Bool
  | .empty => []
  | .one xs => xs.reverse
  | .both _ ys => ys.reverse

example : ∃ b, Realizes taggedReverse b := ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (taggedSwap (α := α))
      (fun _ => 20) (fun n => k * (n + 2)) := by
  model_fun_prop

def swapIf {α : Type*} (x : Bool × α × α) : α × α :=
  if x.1 then (x.2.2, x.2.1) else x.2

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (swapIf (α := α))
      (fun _ => 20) (fun n => k * (n + 2)) := by
  model_fun_prop

-- Generation checks the budget against the same execution, including the model bridge.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (tailOrEmpty (α := Bool))
        (fun _ => 0) (fun n => k * (n + 2)) := by model_fun_prop
  trivial

-- The same callback is compiled once and used for every element.
example : ∃ b, Realizes (List.map (fun x : Bool => (x, x))) b := by
  exact ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.map (id : α → α))
      (fun n => 26 * n + 19) (fun n => k * (n + 3)) := by
  model_fun_prop

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (List.map (gateClauses (α := α))) b := by
  exact ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (List.map (List.reverse : List α → List α)) b := by
  exact ⟨_, by source_fun_prop⟩

-- Each callback pays its own cost, even when the nested lengths are very uneven.
theorem mapReverse_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.map (List.reverse : List α → List α))
      (fun n => 34 * n + 19) (fun n => k * (n + 3)) := by
  model_fun_prop
  · rename_i xs
    have hsum := List.sum_le_sum (l := xs) (f := List.length)
      (g := fun ys => ⌜ys⌝ₜ.size) (fun ys _ => length_le_codeSize ys)
    have hsize := size_encode_list xs
    simp only [List.sum_map_mul_left]
    omega
  · rename_i xs
    simpa using size_encode_map_le List.reverse xs 1 (by decide) (by simp)
  · intro x hx
    exact size_encode_le_list_of_mem hx

example (m : ℕ) :
    (Implementation.reverse.map (α := List Unit)).bounds.time
      (List.replicate m () :: List.replicate m []) = 47 * m + 49 := by
  simp [mapBounds, reverseBounds]
  omega

-- Only ordinary size arithmetic remains; no generated code appears in this proof.
theorem mapGateClauses_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (List.map (gateClauses (α := α)))
      (fun n => 83 * n + 19) (fun n => k * (4 * n + 3)) := by
  model_fun_prop
  · rename_i xs
    apply size_encode_map_le _ _ 4 (by decide)
    intro x _
    exact gateClauses_size_le x
  · intro x hx
    have := size_encode_le_list_of_mem hx
    omega

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {b : Bounds α} (hf : Realizes f b) :
    ∃ c, Realizes (List.map f) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (List.map (List.map (List.reverse : List α → List α))) b :=
  ⟨_, by source_fun_prop⟩

-- An unregistered callback cannot be treated as a free host-language operation.
example (_f : Bool → Bool) : True := by
  fail_if_success have : ∃ b, Realizes (List.map _f) b := ⟨_, by source_fun_prop⟩
  trivial

def foldReverse {α : Type*} (xs : List α) : List α :=
  xs.foldl (fun acc x => x :: acc) []

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (foldReverse (α := α)) b := ⟨_, by source_fun_prop⟩

theorem foldReverse_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (foldReverse (α := α))
      (fun n => 20 * n + 20) (fun n => k * (2 * n + 5)) := by
  model_fun_prop

theorem foldReverse_ftisp {α : Type*} [UniqueEncoding Tree α] :
    foldReverse (α := α) ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := foldReverse_model (α := α)
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨40, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨7 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

def collectStep {α : Type*} (acc : List α) (x : α) := x :: acc

example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun xs : List α => xs.foldl collectStep []) b := ⟨_, by source_fun_prop⟩

-- Both a registered traversal and a callback returning nil compose through the fold rule.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun xss : List (List α) => xss.foldl (fun acc xs => acc ++ xs) []) b :=
  ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun xs : List Bool =>
    xs.foldl (fun acc x => if x then x :: acc else []) []) b := ⟨_, by source_fun_prop⟩

example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (b : Bounds (β × α)) (hf : Realizes (Function.uncurry f) b) :
    ∃ c, Realizes (fun x : β × List α => x.2.foldl f x.1) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

example (_f : Bool → Bool → Bool) : True := by
  fail_if_success have : ∃ b, Realizes (fun xs : List Bool => xs.foldl _f false) b :=
    ⟨_, by source_fun_prop⟩
  trivial

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β} {b : Bounds (ρ × α)}
    (hf : Realizes (fun x : ρ × α => f x.1 x.2) b) :
    ∃ c, Realizes (fun x : ρ × List α => x.2.map (f x.1)) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

example {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β} {b : Bounds (ρ × β × α)}
    (hf : Realizes (fun x : ρ × β × α => f x.1 x.2.1 x.2.2) b) :
    ∃ c, Realizes (fun x : ρ × β × List α => x.2.2.foldl (f x.1) x.2.1) c := by
  let callback := hf.implementation
  exact ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun x : List Bool × List (List Bool) =>
    x.2.map (fun ys => x.1 ++ ys)) b := ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun x : Bool × List (List Bool) =>
    x.2.map (fun ys => ys.map (fun y => if x.1 then y else x.1))) b :=
  ⟨_, by source_fun_prop⟩

-- Pointwise certificates need not give one implementation for all runtime naturals.
example {f : ℕ → Bool → Bool} {b : ℕ → Bounds Bool}
    (_hf : ∀ e, Realizes (f e) (b e)) : True := by
  fail_if_success have : ∃ c, Realizes (fun x : ℕ × List Bool => x.2.map (f x.1)) c :=
    ⟨_, by source_fun_prop⟩
  trivial

example : ∃ b, Realizes (fun x : Σ n, Fin n × List Bool =>
    x.2.2.map (fun _ => x.2.1.val + 1)) b := ⟨_, by source_fun_prop⟩

def repeatFlag (x : Bool × List Unit) : List Bool := x.2.map (fun _ => x.1)

theorem repeatFlag_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace repeatFlag
    (fun n => 100 * n + 100) (fun n => k * (10 * n + 20)) := by
  model_fun_prop
  all_goals
    rename_i x
    have hx : ⌜x.2⌝ₜ.size ≤ ⌜x⌝ₜ.size := by rcases x with ⟨_, _⟩; simp
    have hm : ⌜x.2.map (fun _ => x.1)⌝ₜ.size ≤ 3 * ⌜x.2⌝ₜ.size := by
      apply size_encode_map_le _ _ 3 (by decide)
      intro a _
      cases a
      cases x.1 <;> simp
    have hu (u : Unit) : ⌜u⌝ₜ.size = 1 := by cases u; rfl
    simp at hm
    simp (disch := omega) [hu, ← Nat.max_assoc, Nat.add_comm]
    intros
    omega

theorem repeatFlag_ftisp : repeatFlag ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := repeatFlag_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨200, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨30 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

theorem accumulateGate_ftisp : accumulateGate ∈ FTISP .tree (fun _ => 1) (fun n => n) := by
  obtain ⟨k, hk⟩ := accumulateGate_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨200, 0, by simp⟩,
    IsBigO.iff_exists_nat.mpr ⟨16 * k, 1, ?_⟩⟩
  intro n hn
  nlinarith


theorem circuitStep_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace circuitStep
      (fun n => 28 * n + 304) (fun n => k * (12 * n + 22)) := by
  apply circuitStep_realizes.computableInTimeAndSpace
  rintro ⟨input, acc⟩
  simp
  omega

theorem circuitStep_ftisp : circuitStep ∈ FTISP .tree (fun n => n) (fun n => n) := by
  obtain ⟨k, hk⟩ := circuitStep_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨332, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨34 * k, 1, ?_⟩⟩
  · intro n hn; omega
  · intro n hn; nlinarith

end ComplexityTest.SourceTranslation.Examples
