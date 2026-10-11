/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Implementation
public import Complexity.Models.TreeMachine.Language.List

/-! # Certified traversal with joint source values and resources -/

@[expose] public section

open Complexity TreeProgram TreeProgram.Code
namespace Complexity.TreeProgram.Source

namespace Costed
universe u v
variable {α : Type u} {β : Type v}

/-- Callback costs and the intermediate accumulator share one ordinary monadic fold. -/
def foldl [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (xs : List α) : Costed β :=
  (xs.foldlM (fun a x => (ofValue a ⟨0, ⌜(a, x)⌝ₜ.size⟩).bind (fun a => f a x)) a).bind
    (fun a => ofValue a ⟨0, ⌜a⌝ₜ.size⟩)

@[simp] theorem foldl_nil [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) : foldl f a [] = ofValue a ⟨0, ⌜a⌝ₜ.size⟩ := rfl

theorem foldl_cons [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (x : α) (xs : List α) :
    foldl f a (x :: xs) =
      (ofValue a ⟨0, ⌜(a, x)⌝ₜ.size⟩).bind fun a => (f a x).bind fun a => foldl f a xs := by
  simp only [foldl, List.foldlM_cons]
  simp only [← bindM_eq_bind, bind_assoc]

@[simp] theorem value_foldl [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (xs : List α) :
    (foldl f a xs).value = xs.foldl (fun a x => (f a x).value) a := by
  induction xs generalizing a <;> simp [foldl_cons, *]

@[simp] theorem time_foldl_cons [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (x : α) (xs : List α) :
    (foldl f a (x :: xs)).cost.time = (f a x).cost.time + (foldl f (f a x).value xs).cost.time := by
  simp [foldl_cons]

@[simp] theorem peak_foldl_cons [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (x : α) (xs : List α) :
    (foldl f a (x :: xs)).cost.peak =
      max ⌜(a, x)⌝ₜ.size (max (f a x).cost.peak (foldl f (f a x).value xs).cost.peak) := by
  simp [foldl_cons]

/-- If callback time ignores the accumulator, each element contributes exactly its own budget. -/
theorem time_foldl_eq_sum {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (time : α → ℕ) (a : β) (xs : List α)
    (h : ∀ a x, (f a x).cost.time = time x) :
    (Costed.foldl f a xs).cost.time = (xs.map time).sum := by
  induction xs generalizing a <;> simp [*]

theorem size_le_foldl [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (xs : List α) :
    ⌜a⌝ₜ.size ≤ (foldl f a xs).cost.peak := by
  cases xs <;> simp
  omega

/-- One invariant proves the reached value and both resource bounds. -/
theorem foldl_spec [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (I : List α → β → Prop) (remaining : List α → β → ℕ)
    (space : ℕ) (xs : List α) (a : β) (initial : I xs a)
    (step : ∀ x rest a, I (x :: rest) a →
      I rest (f a x).value ∧
      (f a x).cost.time + remaining rest (f a x).value ≤ remaining (x :: rest) a ∧
      ⌜(a, x)⌝ₜ.size ≤ space ∧ (f a x).cost.peak ≤ space)
    (stop : ∀ a, I [] a → ⌜a⌝ₜ.size ≤ space) :
    I [] (foldl f a xs).value ∧
    (foldl f a xs).cost.time ≤ remaining xs a ∧ (foldl f a xs).cost.peak ≤ space := by
  induction xs generalizing a with
  | nil => simpa using And.intro initial (stop a initial)
  | cons x xs ih =>
    obtain ⟨hi, ht, hs, hp⟩ := step x xs a initial
    obtain ⟨hi', ht', hs'⟩ := ih (f a x).value hi
    rw [foldl_cons]
    simp only [value_bind, value_ofValue, cost_bind, cost_ofValue, Cost.mul_time,
      Cost.mul_peak, Nat.zero_add, max_le_iff]
    exact ⟨hi', (Nat.add_le_add_left ht' _).trans ht, hs, hp, hs'⟩

/-- Include list-traversal overhead and the initial input in a fold evaluation. -/
def evaluateFold [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → Costed β) (a : β) (xs : List α) : Costed β :=
  let run := foldl f a xs
  ofValue run.value ⟨run.cost.time + 13 * xs.length + 10, max ⌜(a, xs)⌝ₜ.size run.cost.peak⟩

@[simp] theorem value_mapM (f : α → Costed β) (xs : List α) :
    (xs.mapM f).value = xs.map (fun x => (f x).value) := by
  induction xs <;> simp [*]

@[simp] theorem time_mapM (f : α → Costed β) (xs : List α) :
    (xs.mapM f).cost.time = (xs.map (fun x => (f x).cost.time)).sum := by
  induction xs <;> simp [*]

@[simp] theorem peak_mapM (f : α → Costed β) (xs : List α) :
    (xs.mapM f).cost.peak = xs.foldr (fun x s => max (f x).cost.peak s) 0 := by
  induction xs <;> simp [*]

/-- The standard map traversal keeps its input and produced output in addition to callback peaks. -/
def evaluateMap [UniqueEncoding Tree β] (f : α → Costed β) (xs : List α)
    (overhead inputSize : ℕ) : Costed (List β) :=
  let run := xs.mapM f
  ofValue run.value
    ⟨run.cost.time + overhead, max inputSize (max (⌜run.value⌝ₜ.size + 1) run.cost.peak)⟩

@[simp] theorem value_evaluateMap [UniqueEncoding Tree β]
    (f : α → Costed β) (xs : List α) (overhead inputSize : ℕ) :
    (evaluateMap f xs overhead inputSize).value = xs.map (fun x => (f x).value) := by
  simp [evaluateMap]

@[simp] theorem time_evaluateMap [UniqueEncoding Tree β]
    (f : α → Costed β) (xs : List α) (overhead inputSize : ℕ) :
    (evaluateMap f xs overhead inputSize).cost.time =
      (xs.map (fun x => (f x).cost.time)).sum + overhead := by
  simp [evaluateMap]

@[simp] theorem peak_evaluateMap [UniqueEncoding Tree β]
    (f : α → Costed β) (xs : List α) (overhead inputSize : ℕ) :
    (evaluateMap f xs overhead inputSize).cost.peak =
      max inputSize (max (⌜xs.map (fun x => (f x).value)⌝ₜ.size + 1)
        (xs.foldr (fun x s => max (f x).cost.peak s) 0)) := by
  simp [evaluateMap]


end Costed

/-- Source-level projection of the joint fold: sum callback times and retain every peak. -/
def foldlCost {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (b : β → α → Cost) (a : β) (xs : List α) : Cost :=
  (Costed.foldl (fun a x => Costed.ofValue (f a x) (b a x)) a xs).cost

@[simp] theorem foldlCost_nil {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (b : β → α → Cost) (a : β) :
    foldlCost f b a [] = ⟨0, ⌜a⌝ₜ.size⟩ := rfl

@[simp] theorem foldlCost_cons {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (b : β → α → Cost) (a : β) (x : α) (xs : List α) :
    foldlCost f b a (x :: xs) =
      ⟨(b a x).time + (foldlCost f b (f a x) xs).time,
        max ⌜(a, x)⌝ₜ.size (max (b a x).peak (foldlCost f b (f a x) xs).peak)⟩ := by
  ext <;> simp [foldlCost]

/-- Source invariants discharge both fold budgets without referring to generated code. -/
theorem foldlCost_le {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : β → α → β} {b : β → α → Cost} (I : List α → β → Prop)
    (remaining : List α → β → ℕ) (space : ℕ) (xs : List α) (a : β)
    (initial : I xs a)
    (step : ∀ x rest a, I (x :: rest) a → I rest (f a x) ∧
      (b a x).time + remaining rest (f a x) ≤ remaining (x :: rest) a ∧
      ⌜(a, x)⌝ₜ.size ≤ space ∧ (b a x).peak ≤ space)
    (stop : ∀ a, I [] a → ⌜a⌝ₜ.size ≤ space) :
    I [] (xs.foldl f a) ∧ (foldlCost f b a xs).time ≤ remaining xs a ∧
      (foldlCost f b a xs).peak ≤ space := by
  simpa only [Costed.value_ofValue, Costed.cost_ofValue, Costed.value_foldl, foldlCost] using
    Costed.foldl_spec (fun a x => Costed.ofValue (f a x) (b a x))
      I remaining space xs a initial step stop

/-- Accumulator-independent callback times add once per element. -/
@[simp] theorem foldlCost_time_sum {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (time : α → ℕ) (peak : β → α → ℕ) (a : β) (xs : List α) :
    (foldlCost f (fun a x => ⟨time x, peak a x⟩) a xs).time = (xs.map time).sum :=
  Costed.time_foldl_eq_sum _ time a xs (by intros; rfl)

/-- A fold that adds at most its current element needs only the initial accumulator and list. -/
theorem foldlCost_peak_le {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : β → α → β} {b : β → α → Cost} (a : β) (xs : List α)
    (result : ∀ a x, ⌜f a x⌝ₜ.size ≤ ⌜(a, x)⌝ₜ.size)
    (peak : ∀ a x, (b a x).peak ≤ ⌜(a, x)⌝ₜ.size) :
    (foldlCost f b a xs).peak ≤ ⌜a⌝ₜ.size + ⌜xs⌝ₜ.size := by
  have h := foldlCost_le (f := f) (b := b)
    (fun rest acc => ⌜acc⌝ₜ.size + ⌜rest⌝ₜ.size ≤ ⌜a⌝ₜ.size + ⌜xs⌝ₜ.size)
    (fun rest acc => (foldlCost f b acc rest).time)
    (⌜a⌝ₜ.size + ⌜xs⌝ₜ.size) xs a le_rfl ?_ ?_
  · exact h.2.2
  · intro x rest acc hi
    have hr := result acc x
    have hp := peak acc x
    simp only [foldlCost_cons, encode_list_cons, size_encode_prod] at hi hr hp ⊢
    exact ⟨by omega, le_rfl, by omega, by omega⟩
  · intro acc hi
    omega

/-- Fold bounds written solely in terms of the source callback and its input-dependent bounds. -/
@[simps] def foldlSumBounds {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (b : Bounds (β × α)) : Bounds (β × List α) :=
  let b' a x : Cost := ⟨b.time (a, x), b.peak (a, x)⟩
  ⟨fun x => (foldlCost f b' x.1 x.2).time + 13 * x.2.length + 10,
    fun x => max ⌜x⌝ₜ.size (foldlCost f b' x.1 x.2).peak⟩

namespace Traversal

private theorem foldlStep_bounded {α β : Type*} {time space : ℕ}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (p : Value → Value → Code Value) (x : α) (a : β)
    (hpFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((p a v).build n).2.1)
    (rest acc : Var) (n : ℕ) (s : ℕ → Tree) (xs : List α)
    (hp : ∀ b v m t, n ≤ m → (∀ j < n, t j = s j) →
      b.expression.bound ≤ m → v.expression.bound ≤ m →
      b.eval t = ⌜a⌝ₜ → v.eval t = ⌜x⌝ₜ →
      (p b v).Bounded m t time space (fun w u =>
        w.eval u = ⌜f a x⌝ₜ ∧ ∀ j < m, u j = t j))
    (ha : acc.index < n) (hne : rest.index ≠ acc.index)
    (hsr : rest.get s = ⌜x :: xs⌝ₜ) (hsa : acc.get s = ⌜a⌝ₜ)
    (hs : ⌜x :: xs⌝ₜ.size ≤ space) (haSize : ⌜a⌝ₜ.size ≤ space)
    (ht : ⌜f a x⌝ₜ.size ≤ space) :
    (do
      let r ← read rest
      let x ← r.left
      let a ← read acc
      write acc (← p a x)
      write rest (← r.right)).Bounded n s (time + 10) space (fun _ t =>
        rest.get t = ⌜xs⌝ₜ ∧ acc.get t = ⌜f a x⌝ₜ ∧
        ∀ j < n, j ≠ rest.index → j ≠ acc.index → t j = s j) := by
  simp only [Var.get] at hsr hsa
  simp only [bounded_read_bind_iff, Var.get, bounded_left_bind_iff,
    Value.eval_var, Function.update_self]
  simp +contextual (disch := omega) only [encode_list_cons, encode_prod, Tree.size_pair,
    Nat.le_add_left, hsr, Nat.reduceSubDiff, Nat.add_one_sub_one, Tree.left_pair,
    Function.update_of_ne, hsa, Value.right, Value.expression.eq_2, ne_eq, true_and,
    and_self_left] at hs ht ⊢
  refine ⟨by omega, by omega, ?_⟩
  have hn := hpFresh (.var (n + 2)) (.var (n + 1)) (n + 3)
    (by change n + 2 + 1 ≤ n + 3; omega) (by change n + 1 + 1 ≤ n + 3; omega)
  apply Code.Bounded.bind (hp (.var (n + 2)) (.var (n + 1)) (n + 3) _
    (by omega)
    (by intros; simp (disch := omega))
    (by change n + 2 + 1 ≤ n + 3; omega)
    (by change n + 1 + 1 ≤ n + 3; omega) (by simp) (by simp))
  intro w t ⟨hw, hf⟩
  have hsteps := w.assignSteps_le
  have hr' : t n = .pair ⌜x⌝ₜ ⌜xs⌝ₜ := by
    simpa (disch := omega) using hf n (by omega)
  simp +contextual (disch := omega) [hw, hr', hf]
  omega

theorem foldl_budget_bounded {α β : Type*} {space : ℕ}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (p : Value → Value → Code Value)
    (hpFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((p a v).build n).2.1)
    (cost : β → α → ℕ) (budget : List α → β → ℕ)
    (I : List α → β → Prop) (xs : List α) (a : β) (init v : Value) (n : ℕ) (s : ℕ → Tree)
    (hI : I xs a)
    (hstep : ∀ x as b, I (x :: as) b → I as (f b x))
    (hbudget : ∀ x as b, I (x :: as) b →
      cost b x + 12 + budget as (f b x) ≤ budget (x :: as) b)
    (hsize : ∀ as b, I as b → ⌜as⌝ₜ.size ≤ space ∧ ⌜b⌝ₜ.size ≤ space)
    (hp : ∀ x as b, I (x :: as) b → ∀ w v m t, n ≤ m → (∀ j < n, t j = s j) →
      w.expression.bound ≤ m → v.expression.bound ≤ m → w.eval t = ⌜b⌝ₜ → v.eval t = ⌜x⌝ₜ →
      (p w v).Bounded m t (cost b x) space (fun z u =>
        z.eval u = ⌜f b x⌝ₜ ∧ ∀ j < m, u j = t j))
    (hv : v.expression.bound ≤ n) (hx : v.eval s = ⌜xs⌝ₜ) (ha : init.eval s = ⌜a⌝ₜ) :
    (List.Code.foldl p init v).Bounded n s
      (budget xs a + init.expression.assignSteps + 6) space
      (fun w t => w.eval t = ⌜xs.foldl f a⌝ₜ ∧ ∀ j < n, t j = s j) := by
  have hv' := (v.eval_update_of_bound_le hv s ⌜a⌝ₜ).trans hx
  have hvTime := v.assignSteps_le
  obtain ⟨hs, hb⟩ := hsize xs a hI
  simp only [List.Code.foldl, List.Code.forEach, bind_assoc, bounded_newVar_bind_iff, ha, hv']
  refine ⟨by omega, hb, by omega, hs, ?_⟩
  let u := Function.update (Function.update s n ⌜a⌝ₜ) (n + 1) ⌜xs⌝ₜ
  let J (t : ℕ → Tree) (k : ℕ) := ∃ as b,
    t (n + 1) = ⌜as⌝ₜ ∧ t n = ⌜b⌝ₜ ∧ I as b ∧
      as.foldl f b = xs.foldl f a ∧ (∀ j < n, t j = s j) ∧ k = budget as b + 2
  have hl := Bounded.whileNode_budget (n := n + 2) (s := u) (space := space) ⟨n + 1⟩
    (do
      let r ← read ⟨n + 1⟩
      let x ← r.left
      let a ← read ⟨n⟩
      write ⟨n⟩ (← p a x)
      write ⟨n + 1⟩ (← r.right)) J (budget xs a + 2)
    ⟨xs, a, by simp [u], by simp [u], hI, rfl,
      (by intros; simp (disch := omega) [u]), rfl⟩
    (by rintro t k ⟨as, b, hr, _, hi, _⟩; simpa [Var.get, hr] using (hsize as b hi).1)
    (by rintro t k ⟨as, b, _, _, _, _, _, rfl⟩ _; omega)
    (by
      rintro t k ⟨as, b, hr, hb, hi, heq, hf, rfl⟩ hroot
      cases as with
      | nil => simp [Var.get, hr, encode_unit] at hroot
      | cons x as =>
        have hi' := hstep x as b hi
        refine ⟨cost b x + 10, ?_⟩
        apply (foldlStep_bounded f p x b hpFresh
          ⟨n + 1⟩ ⟨n⟩ (n + 2) t as
          (fun w v m u hm hframe => hp x as b hi w v m u (by omega)
            (fun j hj => (hframe j (by omega)).trans (hf j hj)))
          (by simp) (by simp) hr hb
          (hsize _ _ hi).1 (hsize _ _ hi).2 (hsize _ _ hi').2).mono le_rfl le_rfl
        rintro _ v ⟨hvr, hva, hvf⟩
        refine ⟨budget as (f b x) + 2, ⟨as, f b x, hvr, hva, hi', heq, ?_, rfl⟩, ?_⟩
        · intro j hj
          exact (hvf j (by omega) (by change j ≠ n + 1; omega)
            (by change j ≠ n; omega)).trans (hf j hj)
        · have := hbudget x as b hi; omega)
  apply Bounded.mono (time := (budget xs a + 2) + 2) ?_
    (by omega) le_rfl (fun _ _ h => h)
  apply Bounded.bind (by simpa [u] using hl)
  rintro _ t ⟨⟨k, as, b, hr, hb, hi, heq, hf, _⟩, hstop⟩
  cases as with
  | cons x as => simp [hr, encode_prod] at hstop
  | nil =>
    have hpos := (hsize [] b hi).2
    have hn := hpFresh (.var (n + 4)) (.var (n + 3)) (n + 5)
      (by change n + 4 + 1 ≤ n + 5; omega) (by change n + 3 + 1 ≤ n + 5; omega)
    simp only [List.foldl_nil] at heq
    simp only [bounded_read_iff, Var.get_mk, hb, heq, Value.eval_var,
      Function.update_self, Nat.add_assoc, Nat.reduceAdd, le_refl, true_and]
    refine ⟨by simpa [heq] using hpos, ?_⟩
    intro j hj
    change Function.update t (((p (.var (n + 4)) (.var (n + 3))).build (n + 5)).2.1 + 1)
      ⌜xs.foldl f a⌝ₜ j = s j
    rw [Function.update_of_ne (by omega)]
    exact hf j hj


/-- Map one callback over a list while retaining its shared environment. -/
def mapDependentProgram (p : Value → Code Value) (v : Value) : Code Value := do
  let e ← v.left
  let xs ← v.right
  List.Code.map (fun x => do p (← e.pair x)) xs

/-- Unpack the initial accumulator and list before running a fold callback. -/
def foldProgram (p : Value → Code Value) (v : Value) : Code Value := do
  let a ← v.left
  let xs ← v.right
  List.Code.foldl (fun a x => do p (← a.pair x)) a xs

end Traversal

theorem Implements.foldl {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {run : β → α → Costed β}
    (hf : Implements p (fun x => (run x.1 x.2).value)
      (Costed.bounds (fun x : β × α => run x.1 x.2))) :
    Implements (Traversal.foldProgram p)
      (fun x : β × List α => (Costed.evaluateFold run x.1 x.2).value)
      (Costed.bounds (fun x : β × List α => Costed.evaluateFold run x.1 x.2)) := by
  obtain ⟨hpFresh, hp⟩ := hf
  let f (a : β) (x : α) := (run a x).value
  let q (a x : Value) := do p (← a.pair x)
  have hqFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((q a v).build n).2.1 := by
    intro a v n _ _
    have := (hpFresh (.var n) (n + 1) (by change n + 1 ≤ n + 1; omega)).1
    change n ≤ ((p (.var n)).build (n + 1)).2.1
    omega
  constructor
  · intro v n hv
    have := (hpFresh (.var (n + 7)) (n + 8) (by change n + 7 + 1 ≤ n + 8; omega)).1
    change n ≤ ((p (.var (n + 7))).build (n + 8)).2.1 + 2 ∧
      ((p (.var (n + 7))).build (n + 8)).2.1 + 1 + 1 ≤
        ((p (.var (n + 7))).build (n + 8)).2.1 + 2
    omega
  · intro v n s ⟨a, xs⟩ hv hx
    let budget as c := (Costed.foldl run c as).cost.time + 13 * as.length
    let space := max ⌜(a, xs)⌝ₜ.size (Costed.foldl run a xs).cost.peak
    let I (as : List α) (c : β) := ⌜as⌝ₜ.size ≤ space ∧
      (Costed.foldl run c as).cost.peak ≤ space
    have hx' := (v.eval_update_of_bound_le hv s ⌜a⌝ₜ).trans hx
    have hs : ⌜(a, xs)⌝ₜ.size ≤ space := Nat.le_max_left _ _
    change (Traversal.foldProgram p v).Bounded n s (budget xs a + 10) space _
    simp only [Traversal.foldProgram]
    simp only [bounded_left_bind_iff, hx, encode_prod, Tree.left_pair,
      bounded_right_bind_iff, hx', Tree.right_pair]
    refine ⟨by omega, hs, by omega, hs, ?_⟩
    apply (Traversal.foldl_budget_bounded f q hqFresh (fun c x => (run c x).cost.time + 1)
      budget I xs a (.var n) (.var (n + 1))
      (n + 2) _ ?_ ?_ ?_ ?_ ?_ (by change n + 1 + 1 ≤ n + 2; omega)
      (by simp) (by simp)).mono (by simp) le_rfl
    · intro w t ⟨hw, hf⟩
      refine ⟨by simpa [Costed.evaluateFold, Costed.value_foldl, f] using hw, ?_⟩
      intro j hj
      simpa (disch := omega) using hf j (by omega)
    · refine ⟨?_, Nat.le_max_right _ _⟩
      simp only [size_encode_prod] at hs; omega
    · rintro x as c ⟨hs, hp⟩
      simp only [Costed.peak_foldl_cons, Nat.max_le] at hp
      refine ⟨?_, hp.2.2⟩
      simp only [encode_list_cons, size_encode_prod] at hs; omega
    · intro x as c _
      simp only [budget, Costed.time_foldl_cons, f, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rintro as c ⟨hs, hc⟩
      exact ⟨hs, (Costed.size_le_foldl run c as).trans hc⟩
    · rintro x as c ⟨_, hs⟩ a v n s _ _ ha hv hc hx
      simp only [Costed.peak_foldl_cons, Nat.max_le] at hs
      simp only [q, bounded_pair_bind_iff]
      refine ⟨by omega, ?_, ?_⟩
      · simpa only [hc, hx, ← encode_prod] using hs.1
      · apply (hp (.var n) (n + 1) _ (c, x) (by change n + 1 ≤ n + 1; omega)
          (by simp [hc, hx, encode_prod])).mono (by simp) hs.2.1
        intro w t ⟨hw, hf⟩
        refine ⟨hw, ?_⟩
        intro j hj
        simpa (disch := omega) using hf j (by omega)


/-- Fold a certified callback while jointly evaluating source values and resources. -/
@[simps program evaluate] def Implementation.foldl {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : β → α → β}
    (hf : Implementation (Function.uncurry f)) :
    Implementation (fun x : β × List α => x.2.foldl f x.1) where
  program := Traversal.foldProgram hf.program
  evaluate x := Costed.evaluateFold (fun a x => hf.evaluate (a, x)) x.1 x.2
  value_eq x := by simp [Costed.evaluateFold, hf.value_eq, Function.uncurry_def]
  sound := hf.sound.foldl

@[simp, source_bounds↓] theorem Implementation.bounds_foldl {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : β → α → β}
    (hf : Implementation (Function.uncurry f)) :
    hf.foldl.bounds = foldlSumBounds f hf.bounds := by
  have callback : (fun a x => hf.evaluate (a, x)) =
      fun a x => Costed.ofValue (f a x) ⟨hf.bounds.time (a, x), hf.bounds.peak (a, x)⟩ := by
    funext a x
    have hv : (hf.evaluate (a, x)).value = f a x := hf.value_eq (a, x)
    rw [← hv]
    rfl
  simp only [Implementation.bounds, Costed.bounds, Implementation.foldl_evaluate,
    Costed.evaluateFold, callback, foldlSumBounds, foldlCost, Costed.cost_ofValue]

end Complexity.TreeProgram.Source
