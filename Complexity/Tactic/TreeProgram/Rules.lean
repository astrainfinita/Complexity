/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Traversal
public import Complexity.Tactic.TreeProgram.Registration
public import Complexity.Models.TreeMachine.Language.Nat
public import Complexity.Encoding.Sigma
public import Complexity.Encoding.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Source-function primitive and resource-combination rules -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

@[simp] theorem size_encode_reverse {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    (encode Tree xs.reverse).size = (encode Tree xs).size := by
  simpa using Tree.size_reverseAppend ⌜xs⌝ₜ ⌜([] : List α)⌝ₜ

grind_pattern size_encode_list_append => ⌜xs ++ ys⌝ₜ.size
grind_pattern size_encode_reverse => ⌜xs.reverse⌝ₜ.size

theorem length_le_codeSize {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    xs.length ≤ (encode Tree xs).size := by
  rw [size_encode_list]
  omega

/-- Bounds for reversing an encoded list. -/
@[simps -fullyApplied] def reverseBounds {α : Type*} [UniqueEncoding Tree α] : Bounds (List α) :=
  ⟨fun xs => 13 * xs.length + 8, fun xs => ⌜xs⌝ₜ.size + 1⟩

attribute [source_bounds↓] reverseBounds_time reverseBounds_peak

/-- A certified linear-time reversal, without traversing the encoded elements. -/
def Implementation.reverse {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.reverse : List α → List α) :=
  .ofImplements List.Code.reverse reverseBounds ⟨fun v n _ => by
      change n ≤ n + 8 ∧ n + 7 + 1 ≤ n + 8
      omega,
    fun v n s xs _ hx => by
      apply (List.Code.reverse_bounded v n s).mono
      · simp [hx]
      · simp [hx]
      · intro w t ⟨hw, hframe⟩
        refine ⟨?_, hframe⟩
        rw [hx] at hw
        simpa using hw.trans (reverseAppend_encode_list xs ([] : List α))⟩

@[simp, source_bounds↓] theorem Implementation.bounds_reverse {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.reverse (α := α)).bounds = reverseBounds := rfl

/-- Backend contract for a primitive receiving two source-value handles. -/
def BinarySpec {α β γ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    (p : Value → Value → Code Value) (f : α → β → γ) (cost : Bounds (α × β)) : Prop :=
  (∀ u v n, u.expression.bound ≤ n → v.expression.bound ≤ n →
    n ≤ ((p u v).build n).2.1 ∧ ((p u v).build n).1.expression.bound ≤ ((p u v).build n).2.1) ∧
  ∀ u v n s x y, u.expression.bound ≤ n → v.expression.bound ≤ n →
    u.eval s = ⌜x⌝ₜ → v.eval s = ⌜y⌝ₜ →
    (p u v).Bounded n s (cost.time (x, y)) (cost.peak (x, y))
      (fun w t => w.eval t = ⌜f x y⌝ₜ ∧ ∀ j < n, t j = s j)

theorem Implements.binary {α β γ δ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] [UniqueEncoding Tree γ] [UniqueEncoding Tree δ]
    {f : α → β} {g : α → γ} {op : β → γ → δ} {b c : Bounds α} {d : Bounds (β × γ)}
    {p q : Value → Code Value} {r : Value → Value → Code Value} (hr : BinarySpec r op d)
    (hf : Implements p f b) (hg : Implements q g c) :
    Implements (fun v => do let w ← p v; let z ← q v; r w z) (fun x => op (f x) (g x))
      ⟨fun x => b.time x + (c.time x + d.time (f x, g x)),
       fun x => max (b.peak x) (max (c.peak x) (d.peak (f x, g x)))⟩ := by
  obtain ⟨hpFresh, hp⟩ := hf
  obtain ⟨hqFresh, hq⟩ := hg
  constructor
  · intro v n hv
    obtain ⟨hn, hw⟩ := hpFresh v n hv
    obtain ⟨hm, hz⟩ := hqFresh v _ (hv.trans hn)
    obtain ⟨hl, hu⟩ := hr.1 _ _ _ (hw.trans hm) hz
    exact ⟨hn.trans (hm.trans hl), hu⟩
  · intro v n s x hv hx
    obtain ⟨hn, hw⟩ := hpFresh v n hv
    apply Code.Bounded.bind ((hp v n s x hv hx).with_result.mono le_rfl
      (Nat.le_max_left _ _) (fun _ _ h => h))
    rintro w t ⟨rfl, hwVal, ht⟩
    obtain ⟨hm, hz⟩ := hqFresh v _ (hv.trans hn)
    apply Code.Bounded.bind ((hq v _ t x (hv.trans hn)
      ((v.eval_eq_of_forall_lt hv ht).trans hx)).with_result.mono le_rfl
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) (fun _ _ h => h))
    rintro z u ⟨rfl, hzVal, hu⟩
    apply (hr.2 _ _ _ u (f x) (g x) (hw.trans hm) hz
      ((((p v).build n).1.eval_eq_of_forall_lt hw hu).trans hwVal) hzVal).mono
        le_rfl ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
    intro a w ⟨ha, hw⟩
    exact ⟨ha, fun j hj => (hw j ((hj.trans_le hn).trans_le hm)).trans
      ((hu j (hj.trans_le hn)).trans (ht j hj))⟩

/-- Apply a primitive to the results of two certified implementations. -/
def Implementation.binary {α β γ δ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] [UniqueEncoding Tree γ] [UniqueEncoding Tree δ]
    {f : α → β} {g : α → γ} {op : β → γ → δ} {d : Bounds (β × γ)}
    {r : Value → Value → Code Value} (hr : BinarySpec r op d)
    (hf : Implementation f) (hg : Implementation g) : Implementation (fun x => op (f x) (g x)) where
  program v := do let w ← hf.program v; let z ← hg.program v; r w z
  evaluate x := (hf.evaluate x).bind fun a => (hg.evaluate x).bind fun b =>
    Costed.ofValue (op a b) ⟨d.time (a, b), d.peak (a, b)⟩
  value_eq x := by simp [hf.value_eq, hg.value_eq]
  sound := Implements.binary hr hf.sound hg.sound

@[simp, source_bounds↓] private theorem Implementation.bounds_binary {α β γ δ : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ] [UniqueEncoding Tree δ]
    {f : α → β} {g : α → γ} {op : β → γ → δ} {d : Bounds (β × γ)}
    {r : Value → Value → Code Value} (hr : BinarySpec r op d)
    (hf : Implementation f) (hg : Implementation g) :
    (binary hr hf hg).bounds =
      ⟨fun x => hf.bounds.time x + (hg.bounds.time x + d.time (f x, g x)),
       fun x => max (hf.bounds.peak x) (max (hg.bounds.peak x) (d.peak (f x, g x)))⟩ := by
  ext x <;> simp [bounds, binary, hf.value_eq, hg.value_eq]

theorem pair_spec {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    BinarySpec Value.pair (Prod.mk : α → β → α × β) ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩ := by
  constructor
  · intro u v n hu hv
    exact ⟨Nat.le_succ _, le_rfl⟩
  · intro u v n s x y hu hv hx hy
    simp +contextual (disch := omega) [hx, hy, encode_prod]

theorem append_spec {α : Type*} [UniqueEncoding Tree α] :
    BinarySpec List.Code.append (fun x y : List α => x ++ y)
      ⟨fun x => 26 * x.1.length + 16, fun x => ⌜x.1⌝ₜ.size + ⌜x.2⌝ₜ.size⟩ := by
  constructor
  · intro u v n hu hv
    change n ≤ n + 16 ∧ n + 15 + 1 ≤ n + 16
    omega
  · intro u v n s x y hu hv hx hy
    simpa only [hx, hy, listLength_encode_list,
      show (.nil : Tree) = ⌜([] : List α)⌝ₜ from rfl, reverseAppend_encode_list,
      List.append_nil, List.reverse_reverse] using List.Code.append_bounded u v n s hv

/-- Bounds for computing both operands and appending their lists. -/
@[simps] def appendBounds {α β : Type*} [UniqueEncoding Tree β]
    (f g : α → List β) (b c : Bounds α) : Bounds α :=
  ⟨fun xs => b.time xs + (c.time xs + (26 * (f xs).length + 16)),
    fun xs => max (b.peak xs) (max (c.peak xs)
      ((encode Tree (f xs)).size + (encode Tree (g xs)).size))⟩

attribute [source_bounds↓] appendBounds_time appendBounds_peak

/-- Compute two encoded lists and append them. -/
def Implementation.append {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f g : α → List β} (hf : Implementation f) (hg : Implementation g) :
    Implementation (fun x => f x ++ g x) := .binary append_spec hf hg

@[simp, source_bounds↓] theorem Implementation.bounds_append {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f g : α → List β}
    (hf : Implementation f) (hg : Implementation g) :
    (hf.append hg).bounds = appendBounds f g hf.bounds hg.bounds := by
  simp only [append, bounds_binary, appendBounds]

/-- Zero-cost bounds for returning the input value. -/
@[simps -fullyApplied] def identityBounds {α : Type*} : Bounds α := ⟨fun _ => 0, fun _ => 0⟩

attribute [source_bounds↓] identityBounds_time identityBounds_peak


open TreeProgram.Code

private theorem map_bounded {α β : Type*} {space : ℕ}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : α → β) (p : Value → Code Value) (cost : α → ℕ)
    (hpFresh : ∀ v n, v.expression.bound ≤ n → n ≤ ((p v).build n).2.1)
    (xs : List α) (v : Value) (n : ℕ) (s : ℕ → Tree)
    (hp : ∀ x ∈ xs, ∀ v m t, n ≤ m → (∀ j < n, t j = s j) →
      v.expression.bound ≤ m → v.eval t = ⌜x⌝ₜ →
      (p v).Bounded m t (cost x) space (fun w u =>
        w.eval u = ⌜f x⌝ₜ ∧ ∀ j < m, u j = t j))
    (hv : v.expression.bound ≤ n) (hx : v.eval s = ⌜xs⌝ₜ)
    (hs : ⌜xs⌝ₜ.size ≤ space) (ht : ⌜xs.map f⌝ₜ.size + 1 ≤ space) :
    (List.Code.map p v).Bounded n s ((xs.map cost).sum + 26 * xs.length + 15) space
      (fun w t => w.eval t = ⌜xs.map f⌝ₜ ∧ ∀ j < n, t j = s j) := by
  let q (a v : Value) := do Value.pair (← p v) a
  let I (as : List α) (b : List β) := as ⊆ xs ∧ ⌜as⌝ₜ.size ≤ space ∧
    ⌜as.map f⌝ₜ.size + ⌜b⌝ₜ.size ≤ space + 1
  have hqFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((q a v).build n).2.1 := by
    intro a v n _ hv
    have := hpFresh v n hv
    change n ≤ ((p v).build n).2.1 + 1
    omega
  have hfold : (List.Code.foldl q .nil v).Bounded n s ((xs.map cost).sum + 13 * xs.length + 7) space
      (fun w t => w.eval t = ⌜(xs.map f).reverse⌝ₜ ∧ ∀ j < n, t j = s j) := by
    apply (Traversal.foldl_budget_bounded (fun b x => f x :: b) q hqFresh
      (fun _ x => cost x + 1) (fun as _ => (as.map cost).sum + 13 * as.length) I xs []
      .nil v n s ⟨List.Subset.refl _, hs, by simp; omega⟩ ?_ ?_ ?_ ?_ hv hx (by simp)).mono
      (by simp) le_rfl
    · simp
    · rintro x as b ⟨hsub, hs, ht⟩
      refine ⟨fun y hy => hsub (by simp [hy]), ?_, ?_⟩
      · simp only [encode_list_cons, size_encode_prod] at hs; omega
      · simpa only [List.map_cons, encode_list_cons, size_encode_prod, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ht
    · intro x as b _
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    · rintro as b ⟨_, hs, ht⟩
      have := Tree.size_pos ⌜as.map f⌝ₜ
      exact ⟨hs, by omega⟩
    · rintro x as b ⟨hsub, _, ht⟩ a v n s hnBase hsBase ha hv hb hx
      have hn := hpFresh v n hv
      apply Code.Bounded.bind (hp x (hsub (by simp)) v n s hnBase hsBase hv hx)
      intro w t ⟨hw, hf⟩
      have ha' := (a.eval_eq_of_forall_lt ha hf).trans hb
      have := Tree.size_pos ⌜as.map f⌝ₜ
      simp only [List.map_cons, encode_list_cons, size_encode_prod] at ht
      simp +contextual (disch := omega) [hw, ha', hf]
      omega
  simp only [List.Code.map]
  apply Bounded.mono (time := ((xs.map cost).sum + 13 * xs.length + 7) + (13 * xs.length + 8)) ?_
    (by omega) le_rfl (fun _ _ h => h)
  apply Bounded.bind hfold
  intro w t ⟨hw, hf⟩
  apply (List.Code.reverse_bounded _ _ t).mono
  · simp [hw]
  · simpa [hw] using ht
  · intro z u ⟨hz, hframe⟩
    refine ⟨?_, ?_⟩
    · simpa only [hw, show (.nil : Tree) = ⌜([] : List β)⌝ₜ from rfl,
        reverseAppend_encode_list, List.reverse_reverse, List.append_nil] using hz
    · intro j hj
      have hn := hpFresh (.var (n + 3)) (n + 5) (by change n + 3 + 1 ≤ n + 5; omega)
      apply (hframe j ?_).trans (hf j hj)
      change j < ((p (.var (n + 3))).build (n + 5)).2.1 + 3
      omega

@[simp] theorem foldr_max_le {α : Type*} (cost : α → ℕ) (xs : List α) (bound : ℕ) :
    xs.foldr (fun x n => max (cost x) n) 0 ≤ bound ↔ ∀ x ∈ xs, cost x ≤ bound := by
  induction xs <;> simp_all

/-- Map bounds, summing callback times and including traversal overhead. -/
@[simps] def mapBounds {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : α → β) (b : Bounds α) : Bounds (List α) :=
  ⟨fun xs => (xs.map b.time).sum + 26 * xs.length + 15,
    fun xs => max ⌜xs⌝ₜ.size (max (⌜xs.map f⌝ₜ.size + 1)
      (xs.foldr (fun x n => max (b.peak x) n) 0))⟩

theorem Implements.map {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : α → β} {b : Bounds α} (hf : Implements p f b) :
    Implements (List.Code.map p) (List.map f) (mapBounds f b) := by
  obtain ⟨hpFresh, hp⟩ := hf
  constructor
  · intro v n hv
    have hn := (hpFresh (.var (n + 3)) (n + 5) (by change n + 3 + 1 ≤ n + 5; omega)).1
    change n ≤ ((p (.var (n + 3))).build (n + 5)).2.1 + 11 ∧
      ((p (.var (n + 3))).build (n + 5)).2.1 + 10 + 1 ≤
        ((p (.var (n + 3))).build (n + 5)).2.1 + 11
    omega
  · intro v n s xs hv hx
    apply map_bounded f p b.time (fun v n hv => (hpFresh v n hv).1) xs v n s ?_ hv hx
      (Nat.le_max_left _ _) ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    intro x hmem v n s _ _ hv hx
    apply (hp v n s x hv hx).mono le_rfl ?_ (fun _ _ h => h)
    exact ((foldr_max_le b.peak xs _).mp le_rfl x hmem).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))


private theorem map_evaluate_bounds {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] (run : α → Costed β) :
    Costed.bounds (fun xs => Costed.evaluateMap run xs (26 * xs.length + 15) ⌜xs⌝ₜ.size) =
      mapBounds (fun x => (run x).value) (Costed.bounds run) := by
  ext xs <;> simp [Costed.bounds, mapBounds, Nat.add_assoc]

/-- Reuse each callback's result and resources in one ordinary monadic traversal. -/
def Implementation.map {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} (hf : Implementation f) : Implementation (List.map f) where
  program := List.Code.map hf.program
  evaluate xs := Costed.evaluateMap hf.evaluate xs (26 * xs.length + 15) ⌜xs⌝ₜ.size
  value_eq xs := by simp [hf.value_eq]
  sound := by
    simpa only [Costed.value_evaluateMap, map_evaluate_bounds] using hf.sound.map

@[simp, source_bounds↓] theorem Implementation.bounds_map {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} (hf : Implementation f) : hf.map.bounds = mapBounds f hf.bounds := by
  simpa only [Implementation.bounds, Implementation.map, hf.value_eq] using
    map_evaluate_bounds hf.evaluate

/-- Map bounds for a list with a shared, possibly dependent environment. -/
@[simps] def mapDependentBounds {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    (f : (e : ρ) → α e → β) (b : Bounds (Σ e, α e)) : Bounds (Σ e, List (α e)) :=
  ⟨fun x => (x.2.map (fun y => b.time ⟨x.1, y⟩)).sum + 27 * x.2.length + 17,
    fun x => max ⌜x⌝ₜ.size (max (⌜x.2.map (f x.1)⌝ₜ.size + 1)
      (x.2.foldr (fun y s => max (b.peak ⟨x.1, y⟩) s) 0))⟩

theorem Implements.mapDependent {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : (e : ρ) → α e → β} {b : Bounds (Σ e, α e)}
    (hf : Implements p (fun x : Σ e, α e => f x.1 x.2) b) :
    Implements (Traversal.mapDependentProgram p)
      (fun x : Σ e, List (α e) => x.2.map (f x.1))
      (mapDependentBounds f b) := by
  simp only [mapDependentBounds]
  obtain ⟨hpFresh, hp⟩ := hf
  let q (e x : Value) := do p (← e.pair x)
  have hqFresh (e : Value) : ∀ v n, v.expression.bound ≤ n →
      n ≤ ((q e v).build n).2.1 := by
    intro v n hv
    have h := (hpFresh (.var n) (n + 1) (by change n + 1 ≤ n + 1; omega)).1
    exact (Nat.le_succ n).trans h
  constructor
  · intro v n hv
    have hn := (hpFresh (.var (n + 7)) (n + 8) (by change n + 7 + 1 ≤ n + 8; omega)).1
    change n ≤ ((p (.var (n + 7))).build (n + 8)).2.1 + 11 ∧
      ((p (.var (n + 7))).build (n + 8)).2.1 + 10 + 1 ≤
        ((p (.var (n + 7))).build (n + 8)).2.1 + 11
    omega
  · rintro v n s ⟨e, xs⟩ hv hx
    let space := max ⌜(⟨e, xs⟩ : Σ e, List (α e))⌝ₜ.size (max (⌜xs.map (f e)⌝ₜ.size + 1)
      (xs.foldr (fun x s => max (b.peak ⟨e, x⟩) s) 0))
    have hspace : ⌜(⟨e, xs⟩ : Σ e, List (α e))⌝ₜ.size ≤ space := Nat.le_max_left _ _
    have hout : ⌜xs.map (f e)⌝ₜ.size + 1 ≤ space :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hx' := (v.eval_update_of_bound_le hv s ⌜e⌝ₜ).trans hx
    simp only [Traversal.mapDependentProgram, bounded_left_bind_iff, hx, Sigma.encode_mk,
      encode_prod, Tree.left_pair,
      bounded_right_bind_iff, hx', Tree.right_pair]
    refine ⟨by omega, hspace, by omega, hspace, ?_⟩
    apply (map_bounded (f e) (q (.var n)) (fun x => b.time ⟨e, x⟩ + 1)
      (hqFresh _) xs (.var (n + 1)) (n + 2) _ ?_
      (by change n + 1 + 1 ≤ n + 2; omega) (by simp) ?_ hout).mono ?_ le_rfl ?_
    · intro x hmem w m t hnm hframe hw hx
      have he : (Value.var n).eval t = ⌜e⌝ₜ := by
        simpa (disch := omega) using hframe n (by omega)
      have hpSize := size_encode_le_list_of_mem hmem
      have hpair : ⌜(e, x)⌝ₜ.size ≤ space := by
        simp only [Sigma.encode_mk, size_encode_prod] at hspace ⊢; omega
      simp only [q, bounded_pair_bind_iff, he, hx, ← encode_prod]
      refine ⟨by omega, hpair, ?_⟩
      apply (hp (.var m) (m + 1) _ ⟨e, x⟩
        (by change m + 1 ≤ m + 1; omega) (by simp [Sigma.encode_mk])).mono (by omega) ?_ ?_
      · exact ((foldr_max_le (fun y => b.peak ⟨e, y⟩) xs _).mp le_rfl x hmem).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
      · intro z u ⟨hz, hframe'⟩
        refine ⟨hz, ?_⟩
        intro j hj
        simpa (disch := omega) using hframe' j (by omega)
    · simp only [Sigma.encode_mk, size_encode_prod] at hspace; omega
    · simp [List.sum_map_add, Nat.mul_comm]
      omega
    · intro z u ⟨hz, hframe⟩
      refine ⟨hz, ?_⟩
      intro j hj
      simpa (disch := omega) using hframe j (by omega)

private theorem mapDependent_evaluate_bounds {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    (run : (Σ e, α e) → Costed β) :
    Costed.bounds (fun x : Σ e, List (α e) =>
        Costed.evaluateMap (fun y => run ⟨x.1, y⟩) x.2 (27 * x.2.length + 17) ⌜x⌝ₜ.size) =
      mapDependentBounds (fun e y => (run ⟨e, y⟩).value) (Costed.bounds run) := by
  ext xs <;> simp [Costed.bounds, mapDependentBounds, Nat.add_assoc]

/-- The captured environment is kept once; a single callback handles every runtime index. -/
def Implementation.mapDependent {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} (hf : Implementation (fun x : Σ e, α e => f x.1 x.2)) :
    Implementation (fun x : Σ e, List (α e) => x.2.map (f x.1)) where
  program := Traversal.mapDependentProgram hf.program
  evaluate x := Costed.evaluateMap (fun y => hf.evaluate ⟨x.1, y⟩) x.2
    (27 * x.2.length + 17) ⌜x⌝ₜ.size
  value_eq xs := by simp [hf.value_eq]
  sound := by
    simpa only [Costed.value_evaluateMap, mapDependent_evaluate_bounds] using
      hf.sound.mapDependent (f := fun e y => (hf.evaluate ⟨e, y⟩).value)

@[simp, source_bounds↓] theorem Implementation.bounds_mapDependent {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} (hf : Implementation (fun x : Σ e, α e => f x.1 x.2)) :
    hf.mapDependent.bounds = mapDependentBounds f hf.bounds := by
  simpa only [Implementation.bounds, Implementation.mapDependent, hf.value_eq] using
    mapDependent_evaluate_bounds hf.evaluate

/-- Call code and copy its returned value to a fixed register. -/
def callInto (p : Code Value) (n dest : ℕ) : Cmd ℕ :=
  .seq (Code.block (p.build n).2.2) (.assign dest (p.build n).1.expression)

theorem callInto_bounded {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : α → β} {b : Bounds α} (hf : Implements p f b)
    (v : Value) (n dest : ℕ) (s : ℕ → Tree) (x : α) {time space : ℕ}
    (hv : v.expression.bound ≤ n) (hx : v.eval s = ⌜x⌝ₜ)
    (ht : b.time x ≤ time) (hb : b.peak x ≤ space) (hs : ⌜x⌝ₜ.size ≤ space) :
    (callInto (p v) n dest).Bounded s (time + 2) space
      (fun t => t dest = ⌜f x⌝ₜ ∧ ∀ j < n, j ≠ dest → t j = s j) := by
  apply Cmd.Bounded.seq ((hf.2 v n s x hv hx).mono ht hb (fun _ _ h => h))
  intro t ⟨ho, hframe⟩
  simp only [Cmd.bounded_assign_iff, Value.maxSize_expression, Value.eval_expression]
  exact ⟨Value.assignSteps_le _, ho ▸ (hf.size_le x).trans (max_le hs hb),
    by simp [ho], fun j hj hne => by simpa [hne] using hframe j hj⟩

/-- Compile a tested loop with separate step and final-result programs. -/
def loopCode (test step finish : Value → Code Value) (v : Value) : Code Value :=
  ⟨fun n =>
    let check := callInto (test (.var n)) (n + 2) (n + 1)
    let advance := callInto (step (.var n)) (n + 2) n
    let done := (finish (.var n)).build (n + 2)
    (done.1, max ((test (.var n)).build (n + 2)).2.1
      (max ((step (.var n)).build (n + 2)).2.1 done.2.1),
      [.assign n v.expression, check,
       .while (.var (n + 1)) (.seq advance check), Code.block done.2.2])⟩

/-- A source loop spends the actual step and test allowances from a remaining budget. -/
theorem Implements.loop_budget_finish {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {pc ps pd : Value → Code Value}
    {test : α → Bool} {step : α → α} {finish result : α → β}
    {bc bs bd : Bounds α} (hc : Implements pc test bc) (hs : Implements ps step bs)
    (hd : Implements pd finish bd) (I : α → α → Prop) (budget : α → α → ℕ)
    (space : α → ℕ)
    (hinit : ∀ x, I x x)
    (hsize : ∀ x y, I x y → ⌜y⌝ₜ.size ≤ space x)
    (hcheck : ∀ x y, I x y → bc.peak y ≤ space x)
    (hstop : ∀ x y, I x y → test y = false → bd.time y + 2 ≤ budget x y)
    (hstep : ∀ x y, I x y → test y = true →
      bs.peak y ≤ space x ∧ I x (step y) ∧
        bs.time y + bc.time (step y) + 6 + budget x (step y) ≤ budget x y)
    (hfinish : ∀ x y, I x y → test y = false →
      bd.peak y ≤ space x ∧ finish y = result x) :
    Implements (loopCode pc ps pd) result
      ⟨fun x => bc.time x + budget x x + 4, space⟩ := by
  constructor
  · intro v n hv
    obtain ⟨hn, hr⟩ := hd.1 (.var n) (n + 2) (by change n + 1 ≤ n + 2; omega)
    exact ⟨(by dsimp [loopCode]; omega),
      hr.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩
  · intro v n s x hv hx
    let J (t : ℕ → Tree) (k : ℕ) := ∃ y,
      t n = ⌜y⌝ₜ ∧ t (n + 1) = ⌜test y⌝ₜ ∧ I x y ∧ k = budget x y ∧
      ∀ j < n, t j = s j
    have check (t : ℕ → Tree) (y : α) (hy : t n = ⌜y⌝ₜ) (hi : I x y) :=
      callInto_bounded hc (.var n) (n + 2) (n + 1) t y (by change n + 1 ≤ n + 2; omega) hy
        le_rfl (hcheck x y hi) (hsize x y hi)
    have run (t : ℕ → Tree) (k : ℕ) (hj : J t k) :
        (Cmd.seq (Cmd.while (.var (n + 1))
          (.seq (callInto (ps (.var n)) (n + 2) n)
            (callInto (pc (.var n)) (n + 2) (n + 1))))
          (.seq (Code.block ((pd (.var n)).build (n + 2)).2.2) .skip)).Bounded t k (space x)
          (fun t => ((pd (.var n)).build (n + 2)).1.eval t = ⌜result x⌝ₜ ∧
            ∀ j < n, t j = s j) := by
      apply Cmd.Bounded.loop_budget_seq (.var (n + 1)) J k hj
      · rintro u k ⟨y, hy, hb, hi, _, _⟩
        simpa only [Expr.maxSize, hb] using
          (hc.size_le y).trans (max_le (hsize x y hi) (hcheck x y hi))
      · rintro u k ⟨y, hy, hb, hi, rfl, hf⟩ hr
        have hfalse : test y = false := by simpa [hb] using hr
        have ht := hstop x y hi hfalse
        refine ⟨by simpa only [Expr.steps] using (by omega : 2 ≤ budget x y), ?_⟩
        rw [Cmd.bounded_seq_skip_iff]
        change (pd (.var n)).Bounded (n + 2) u (budget x y - 2) (space x)
          (fun w t => w.eval t = ⌜result x⌝ₜ ∧ ∀ j < n, t j = s j)
        apply (hd.2 (.var n) (n + 2) u y (by change n + 1 ≤ n + 2; omega) hy).mono
          (by simpa only [Expr.steps] using Nat.le_sub_of_add_le ht) (hfinish x y hi hfalse).1
        intro w t ⟨ho, htf⟩
        exact ⟨ho.trans (congrArg (encode Tree) (hfinish x y hi hfalse).2),
          fun j hj => (htf j (by omega)).trans (hf j hj)⟩
      · rintro u k ⟨y, hy, hb, hi, rfl, hf⟩ hr
        obtain ⟨hpeak, hi', ht⟩ := hstep x y hi (by simpa [hb] using hr)
        refine ⟨(bs.time y + 2) + (bc.time (step y) + 2), ?_⟩
        apply Cmd.Bounded.seq (callInto_bounded hs (.var n) (n + 2) n u y
          (by change n + 1 ≤ n + 2; omega) hy le_rfl hpeak (hsize x y hi))
        rintro w ⟨hw, hwf⟩
        apply (check w (step y) hw hi').mono le_rfl le_rfl
        rintro z ⟨hz, hzf⟩
        refine ⟨budget x (step y), ⟨step y, ?_, hz, hi', rfl, ?_⟩, ?_⟩
        · exact (hzf n (by omega) (by omega)).trans hw
        · intro j hj
          exact (hzf j (by omega) (by omega)).trans
            ((hwf j (by omega) (by omega)).trans (hf j hj))
        · simpa only [Expr.steps] using (by omega :
            (bs.time y + 2) + (bc.time (step y) + 2) + 0 + 2 + budget x (step y) ≤ budget x y)
    change (Code.block _).Bounded _ _ _ _
    simp only [loopCode, Code.block]
    apply Cmd.Bounded.mono
      (time := 2 + ((bc.time x + 2) + (budget x x))) ?_
      (by omega) le_rfl (fun _ h => h)
    apply Cmd.Bounded.seq (Q := fun t => t = Function.update s n ⌜x⌝ₜ)
      (by
        simp only [Cmd.bounded_assign_iff, Value.maxSize_expression, Value.eval_expression, hx]
        exact ⟨v.assignSteps_le, hsize x x (hinit x), trivial⟩)
    rintro t rfl
    apply Cmd.Bounded.seq (check _ x (by simp) (hinit x))
    intro t ⟨hflag, hf⟩
    have ht : t n = ⌜x⌝ₜ := by simpa using hf n (by omega) (by omega)
    have hj : J t (budget x x) := ⟨x, ht, hflag, hinit x, rfl, fun j hj => by
      simpa [Nat.ne_of_lt hj] using hf j (by omega) (by omega)⟩
    exact run t _ hj

/-- A source loop spends the actual step and test allowances from a remaining budget. -/
theorem Implements.loop_budget {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {pc ps pd : Value → Code Value}
    {test : α → Bool} {step : α → α} {finish result : α → β}
    {bc bs bd : Bounds α} (hc : Implements pc test bc) (hs : Implements ps step bs)
    (hd : Implements pd finish bd) (I : α → α → Prop) (budget : α → α → ℕ)
    (finishTime space : α → ℕ)
    (hinit : ∀ x, I x x)
    (hsize : ∀ x y, I x y → ⌜y⌝ₜ.size ≤ space x)
    (hcheck : ∀ x y, I x y → bc.peak y ≤ space x)
    (hstop : ∀ x y, I x y → test y = false → 2 ≤ budget x y)
    (hstep : ∀ x y, I x y → test y = true →
      bs.peak y ≤ space x ∧ I x (step y) ∧
        bs.time y + bc.time (step y) + 6 + budget x (step y) ≤ budget x y)
    (hfinish : ∀ x y, I x y → test y = false →
      bd.time y ≤ finishTime x ∧ bd.peak y ≤ space x ∧ finish y = result x) :
    Implements (loopCode pc ps pd) result
      ⟨fun x => bc.time x + budget x x + finishTime x + 4, space⟩ := by
  have h := hc.loop_budget_finish hs hd (result := result) I
    (fun x y => budget x y + finishTime x) space hinit hsize hcheck ?_ ?_ ?_
  · simpa only [← Nat.add_assoc] using h
  · intro x y hi ht
    have := hstop x y hi ht
    have := (hfinish x y hi ht).1
    omega
  · intro x y hi ht
    obtain ⟨hp, hi', hb⟩ := hstep x y hi ht
    exact ⟨hp, hi', by omega⟩
  · intro x y hi ht
    exact (hfinish x y hi ht).2

def Implementation.increment : Implementation BitList.increment := by
  refine .ofImplements Nat.Code.succ
    ⟨fun xs => 28 * xs.length + 25, fun xs => ⌜xs⌝ₜ.size + 5⟩ ⟨?_, ?_⟩
  · intro v n _
    change n ≤ n + 23 ∧ n + 22 + 1 ≤ n + 23
    omega
  · intro v n s xs _ hx
    exact Nat.Code.succ_bits_bounded v n s xs hx

@[simp, source_bounds↓] theorem Implementation.bounds_increment :
    Implementation.increment.bounds =
      ⟨fun xs => 28 * xs.length + 25, fun xs => ⌜xs⌝ₜ.size + 5⟩ := rfl

def Implementation.succ : Implementation Nat.succ :=
  .ofEncode (by intro n; simp) (Implementation.increment.mapInput Nat.bits (fun _ => rfl))

@[simp, source_bounds↓] theorem Implementation.bounds_succ :
    Implementation.succ.bounds =
      ⟨fun a => 28 * a.bits.length + 25, fun a => ⌜a⌝ₜ.size + 5⟩ := rfl

@[source_bounds↓] def Implementation.addOne : Implementation (fun a : ℕ => a + 1) :=
  Implementation.succ

attribute [scoped fun_prop] Implementation.increment Implementation.succ Implementation.addOne

/-- Bounds for selecting a field from an encoded pair. -/
@[simps] def projectionBounds {α : Type*} [UniqueEncoding Tree α] : Bounds α :=
  ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩

attribute [source_bounds↓] projectionBounds_time projectionBounds_peak

/-- Select the first field of an encoded pair. -/
def Implementation.fst {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    Implementation (Prod.fst : α × β → α) := by
  refine .ofImplements Value.left projectionBounds ⟨?_, ?_⟩
  · intro v n hv
    change n ≤ n + 1 ∧ n + 1 ≤ n + 1
    omega
  · intro v n s ⟨x, y⟩ hv hx
    simp +contextual (disch := omega) [projectionBounds, hx]

@[simp, source_bounds↓] theorem Implementation.bounds_fst {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    (Implementation.fst (α := α) (β := β)).bounds = projectionBounds := rfl

/-- Select the second field of an encoded pair. -/
def Implementation.snd {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    Implementation (Prod.snd : α × β → β) := by
  refine .ofImplements Value.right projectionBounds ⟨?_, ?_⟩
  · intro v n hv
    change n ≤ n + 1 ∧ n + 1 ≤ n + 1
    omega
  · intro v n s ⟨x, y⟩ hv hx
    simp +contextual (disch := omega) [projectionBounds, hx]

@[simp, source_bounds↓] theorem Implementation.bounds_snd {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] :
    (Implementation.snd (α := α) (β := β)).bounds = projectionBounds := rfl

/-- Bounds for computing two values and pairing their encodings. -/
@[simps] def pairBounds {α β γ : Type*} [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    (f : α → β) (g : α → γ) (b c : Bounds α) : Bounds α :=
  ⟨fun x => b.time x + (c.time x + 1),
    fun x => max (b.peak x) (max (c.peak x) ⌜(f x, g x)⌝ₜ.size)⟩

attribute [source_bounds↓] pairBounds_time pairBounds_peak

/-- Compute two values and pair their encodings. -/
def Implementation.pair {α β γ : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    {f : α → β} {g : α → γ} (hf : Implementation f) (hg : Implementation g) :
    Implementation (fun x => (f x, g x)) := .binary pair_spec hf hg

@[simp, source_bounds↓] theorem Implementation.bounds_pair {α β γ : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    {f : α → β} {g : α → γ} (hf : Implementation f) (hg : Implementation g) :
    (hf.pair hg).bounds = pairBounds f g hf.bounds hg.bounds := by
  simp only [pair, bounds_binary, pairBounds]


-- The same implementation works for different result types when their encoded outputs coincide.
/-- Return the empty tree representing unit without allocating a register. -/
def Implementation.unit {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun _ : α => ()) := by
  refine .ofImplements (fun _ => pure .nil) identityBounds ⟨?_, ?_⟩
  · intro v n hv
    exact ⟨le_rfl, Nat.zero_le _⟩
  · intro v n s x hv hx
    simp [encode_unit]

@[simp, source_bounds↓] theorem Implementation.bounds_unit {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.unit (α := α)).bounds = identityBounds := rfl

private theorem branch_spec {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p q : Value → Code Value} {f g : α → β} {b c : Bounds α}
    (hf : Implements p f b) (hg : Implements q g c) :
    BinarySpec (fun test v => Bool.Code.matchOn test (q v) (p v))
      (fun (test : Bool) x => if test then f x else g x)
      ⟨fun x => (if x.1 then b.time x.2 else c.time x.2) + 3,
       fun x => max ⌜x.1⌝ₜ.size
         (max ⌜x.2⌝ₜ.size (if x.1 then b.peak x.2 else c.peak x.2))⟩ := by
  constructor
  · intro test v n ht hv
    have hn := (hf.1 v (n + 1) (hv.trans (Nat.le_succ _))).1
    change n ≤ max ((p v).build (n + 1)).2.1
      ((q v).build (n + 1)).2.1 ∧ n + 1 ≤ _
    exact ⟨by omega, hn.trans (Nat.le_max_left _ _)⟩
  · intro test v n s flag x ht hv he hx
    have run {r : Value → Code Value} {h : α → β} {d : Bounds α} (hh : Implements r h d) :
        (r v).Bounded (n + 1) s (d.time x) (max ⌜x⌝ₜ.size (d.peak x))
          (fun w t => (w.eval t).size ≤ max ⌜x⌝ₜ.size (d.peak x) ∧
            (Value.var n).eval (Function.update t n (w.eval t)) = ⌜h x⌝ₜ ∧
            ∀ j < n, Function.update t n (w.eval t) j = s j) := by
      apply (hh.2 v (n + 1) s x (hv.trans (Nat.le_succ _)) hx).mono
        le_rfl (Nat.le_max_right _ _)
      intro w t ⟨hw, hf⟩
      exact ⟨hw ▸ hh.size_le x, by simp [hw], fun j hj => by
        simpa [Nat.ne_of_lt hj] using hf j (hj.trans_le (Nat.le_succ _))⟩
    apply (Code.Bounded.branch (time := if flag then b.time x else c.time x)
      test.expression _ _ _ (by simp [he]) ?_ ?_).mono
      (by simp; omega) le_rfl (fun _ _ h => h)
    · intro h
      have : flag = true := by simpa [he] using h
      subst flag
      exact (run hf).mono le_rfl (Nat.le_max_right _ _)
        (fun _ _ ⟨hs, hq⟩ => ⟨hs.trans (Nat.le_max_right _ _), hq⟩)
    · intro h
      have : flag = false := by simpa [he] using h
      subst flag
      exact (run hg).mono le_rfl (Nat.le_max_right _ _)
        (fun _ _ ⟨hs, hq⟩ => ⟨hs.trans (Nat.le_max_right _ _), hq⟩)

/-- Bounds for evaluating a condition and its selected branch. -/
@[simps] def iteBounds {α : Type*} [UniqueEncoding Tree α]
    (c : α → Bool) (bc bt bf : Bounds α) : Bounds α :=
  ⟨fun x => bc.time x + (if c x then bt.time x else bf.time x) + 3,
    fun x => max ⌜x⌝ₜ.size (max (bc.peak x) (if c x then bt.peak x else bf.peak x))⟩

theorem Implements.ite {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {pc pt pf : Value → Code Value} {c : α → Bool} {f g : α → β}
    {bc bt bf : Bounds α}
    (hc : Implements pc c bc) (ht : Implements pt f bt) (hf : Implements pf g bf) :
    Implements (fun v => do
      let test ← pc v
      Bool.Code.matchOn test (pf v) (pt v))
      (fun x => if c x then f x else g x) (iteBounds c bc bt bf) := by
  apply (Implements.binary (branch_spec ht hf) hc Implementation.identity.implements).mono
  intro x
  have hs := hc.size_le x
  simp only [Implementation.bounds_identity, iteBounds, id_eq,
    Nat.zero_add, Nat.zero_max]
  exact ⟨by omega, by omega⟩

/-- Reuse the condition result and evaluate only the selected branch. -/
@[simps program evaluate] def Implementation.ite {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β}
    (hc : Implementation c) (ht : Implementation f) (hf : Implementation g) :
    Implementation (fun x => if c x then f x else g x) where
  program v := do
    let test ← hc.program v
    Bool.Code.matchOn test (hf.program v) (ht.program v)
  evaluate x :=
    let result := (hc.evaluate x).bind fun test =>
      if test then ht.evaluate x else hf.evaluate x
    Costed.ofValue result.value ⟨result.cost.time + 3, max ⌜x⌝ₜ.size result.cost.peak⟩
  value_eq x := by
    cases h : c x <;> simp [Costed.value_bind, hc.value_eq, ht.value_eq, hf.value_eq, h]
  sound := by
    convert hc.sound.ite ht.sound hf.sound using 1
    · ext x
      cases h : (hc.evaluate x).value <;> simp [Costed.value_bind, h]
    · ext x <;> cases h : (hc.evaluate x).value <;> simp [Costed.bounds, iteBounds, h]

@[simp, source_bounds↓] theorem Implementation.bounds_ite {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Bool} {f g : α → β}
    (hc : Implementation c) (ht : Implementation f) (hf : Implementation g) :
    (hc.ite ht hf).bounds = iteBounds c hc.bounds ht.bounds hf.bounds := by
  ext x <;> cases h : c x <;> simp [bounds, ite_evaluate, hc.value_eq, iteBounds, h]

/-- Ordinary decidable conditions share the Boolean branch implementation and its path budget. -/
def Implementation.iteProp {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Prop} [DecidablePred c] {f g : α → β}
    (hc : Implementation (fun x => decide (c x)))
    (ht : Implementation f) (hf : Implementation g) :
    Implementation (fun x => if c x then f x else g x) :=
  (hc.ite ht hf).congr (by funext x; simp)

@[simp, source_bounds↓] theorem Implementation.bounds_iteProp {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {c : α → Prop} [DecidablePred c] {f g : α → β}
    (hc : Implementation (fun x => decide (c x)))
    (ht : Implementation f) (hf : Implementation g) :
    (hc.iteProp ht hf).bounds =
      iteBounds (fun x => decide (c x)) hc.bounds ht.bounds hf.bounds := by
  simp only [iteProp, bounds_congr, bounds_ite]

attribute [scoped fun_prop] Implementation.iteProp

/-- Summed callback bounds including one shared environment and its traversal overhead. -/
@[simps] def foldlWithBounds {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : ρ → β → α → β) (a : ρ → β) (xs : ρ → List α)
    (bi : Bounds ρ) (bs : Bounds (ρ × β × α)) : Bounds ρ :=
  let costs e := foldlCost (f e) (fun a x => ⟨bs.time (e, a, x), bs.peak (e, a, x)⟩) (a e) (xs e)
  ⟨fun e => bi.time e + (costs e).time + 33 * (xs e).length + 11,
    fun e => max (bi.peak e) (2 * ⌜e⌝ₜ.size + (costs e).peak + 2)⟩

/-- Captured source values travel with the accumulator in one fixed program. -/
def Implementation.foldlWith {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β} {a : ρ → β} {xs : ρ → List α}
    (hi : Implementation (fun e => ((e, a e), xs e)))
    (hs : Implementation (fun p : ρ × β × α => f p.1 p.2.1 p.2.2)) :
    Implementation (fun e => (xs e).foldl (f e) (a e)) := by
  let stepBounds : Bounds ((ρ × β) × α) :=
    ⟨fun p => hs.bounds.time (p.1.1, p.1.2, p.2) + 20,
      fun p => 2 * ⌜p.1.1⌝ₜ.size +
        max ⌜(p.1.2, p.2)⌝ₜ.size (hs.bounds.peak (p.1.1, p.1.2, p.2)) + 2⟩
  let getEnv : Implementation (fun p : (ρ × β) × α => p.1.1) :=
    Implementation.fst.comp Implementation.fst
  let getArgs : Implementation (fun p : (ρ × β) × α => (p.1.1, p.1.2, p.2)) :=
    getEnv.pair ((Implementation.fst.comp Implementation.snd).pair Implementation.snd)
  let step := getEnv.pair (getArgs.comp hs)
  let hstep : Implementation (Function.uncurry
      (fun (ea : ρ × β) (x : α) => (ea.1, f ea.1 ea.2 x))) := step.rebudget stepBounds (by
    rintro ⟨⟨e, a⟩, x⟩
    have hsize := hs.implements.size_le (e, a, x)
    simp only [size_encode_prod, le_max_iff, Function.comp_apply, bounds_pair, pairBounds,
      bounds_comp, compBounds, bounds_fst, projectionBounds, Nat.reduceAdd, bounds_snd,
      Nat.max_assoc, Std.le_refl, true_or, or_true, sup_of_le_right, le_add_iff_nonneg_left,
      zero_le, sup_le_iff, step, getEnv, getArgs, stepBounds] at hsize ⊢
    (repeat' apply And.intro) <;> omega)
  have hcost (e : ρ) (a : β) (xs : List α) :
      (foldlCost (fun ea x => (ea.1, f ea.1 ea.2 x))
          (fun a x => ⟨stepBounds.time (a, x), stepBounds.peak (a, x)⟩) (e, a) xs).time =
        (foldlCost (f e)
          (fun a x => ⟨hs.bounds.time (e, a, x), hs.bounds.peak (e, a, x)⟩) a xs).time +
          20 * xs.length ∧
      (foldlCost (fun ea x => (ea.1, f ea.1 ea.2 x))
          (fun a x => ⟨stepBounds.time (a, x), stepBounds.peak (a, x)⟩) (e, a) xs).peak ≤
        2 * ⌜e⌝ₜ.size + (foldlCost (f e)
          (fun a x => ⟨hs.bounds.time (e, a, x), hs.bounds.peak (e, a, x)⟩) a xs).peak + 2 := by
    induction xs generalizing a with
    | nil => simp; omega
    | cons x xs ih =>
      have := ih (f e a x)
      simp only [foldlCost_cons, stepBounds, size_encode_prod, List.length_cons] at this ⊢
      omega
  have hfold (e : ρ) (a : β) (xs : List α) :
      xs.foldl (fun ea x => (ea.1, f ea.1 ea.2 x)) (e, a) = (e, xs.foldl (f e) a) :=
    List.foldl_hom (fun a => (e, a)) (by intros; rfl)
  let folded := hstep.foldl (f := fun ea x => (ea.1, f ea.1 ea.2 x))
  have hfolded : folded.bounds = foldlSumBounds (fun ea x => (ea.1, f ea.1 ea.2 x)) stepBounds :=
    hstep.bounds_foldl
  let hrun := hi.comp (folded.comp Implementation.snd)
  have hout := hrun.rebudget (foldlWithBounds f a xs hi.bounds hs.bounds) (by
    intro e
    have hc := hcost e (a e) (xs e)
    have hiSize := hi.implements.size_le e
    have hrSize := folded.implements.size_le ((e, a e), xs e)
    simp only [hfolded, foldlSumBounds] at hrSize
    simp only [hrun, Implementation.bounds_comp, Implementation.bounds_snd, hfolded,
      compBounds, foldlSumBounds, foldlWithBounds, projectionBounds]
    constructor
    · nlinarith [hc.1]
    · omega)
  exact hout.congr (by
    funext e
    simpa only [Function.comp_def] using congrArg Prod.snd (hfold e (a e) (xs e)))


@[simp, source_bounds↓] theorem Implementation.bounds_foldlWith {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β} {a : ρ → β} {xs : ρ → List α}
    (hi : Implementation (fun e => ((e, a e), xs e)))
    (hs : Implementation (fun p : ρ × β × α => f p.1 p.2.1 p.2.2)) :
    (hi.foldlWith hs).bounds = foldlWithBounds f a xs hi.bounds hs.bounds := by
  rfl


/-- Compose environment preparation with dependent-map bounds. -/
@[simps!] def mapDependentWithBounds {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    (f : (e : ρ) → α e → β) (xs : (e : ρ) → List (α e))
    (bi : Bounds ρ) (b : Bounds (Σ e, α e)) : Bounds ρ :=
  compBounds (fun e => (⟨e, xs e⟩ : Σ e, List (α e))) bi (mapDependentBounds f b)

/-- The input-producing program and uniform callback compose without choosing new code. -/
def Implementation.mapDependentWith {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} {xs : (e : ρ) → List (α e)}
    (hi : Implementation (fun e => (⟨e, xs e⟩ : Σ e, List (α e))))
    (hf : Implementation (fun p : Σ e, α e => f p.1 p.2)) :
    Implementation (fun e => (xs e).map (f e)) :=
  hi.comp hf.mapDependent

@[simp, source_bounds↓] theorem Implementation.bounds_mapDependentWith {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} {xs : (e : ρ) → List (α e)}
    (hi : Implementation (fun e => (⟨e, xs e⟩ : Σ e, List (α e))))
    (hf : Implementation (fun p : Σ e, α e => f p.1 p.2)) :
    (hi.mapDependentWith hf).bounds = mapDependentWithBounds f xs hi.bounds hf.bounds := by
  rw [mapDependentWith, bounds_comp, bounds_mapDependent]
  rfl

/-- Bounds for a map whose callback shares a runtime environment. -/
@[simps] def mapWithBounds {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : ρ → α → β) (xs : ρ → List α) (bi : Bounds ρ) (b : Bounds (ρ × α)) : Bounds ρ :=
  ⟨fun e => bi.time e + ((xs e).map (fun x => b.time (e, x))).sum + 27 * (xs e).length + 17,
    fun e => max (bi.peak e) (max ⌜(e, xs e)⌝ₜ.size
      (max (⌜(xs e).map (f e)⌝ₜ.size + 1)
        ((xs e).foldr (fun x s => max (b.peak (e, x)) s) 0)))⟩

/-- The constant-family specialization preserves the ordinary captured-map interface. -/
def Implementation.mapWith {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β} {xs : ρ → List α}
    (hi : Implementation (fun e => (e, xs e)))
    (hf : Implementation (fun p : ρ × α => f p.1 p.2)) :
    Implementation (fun e => (xs e).map (f e)) :=
  (hi.mapOutput (fun p => (⟨p.1, p.2⟩ : Σ _ : ρ, List α))
    (fun p => @Sigma.encode_mk ρ (fun _ => List α) _ _ p.1 p.2)).mapDependentWith
    (hf.mapInput (fun p : Σ _ : ρ, α => (p.1, p.2))
      (fun p => (@Sigma.encode_mk ρ (fun _ => α) _ _ p.1 p.2).symm))

@[simp, source_bounds↓] theorem Implementation.bounds_mapWith {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β} {xs : ρ → List α}
    (hi : Implementation (fun e => (e, xs e)))
    (hf : Implementation (fun p : ρ × α => f p.1 p.2)) :
    (hi.mapWith hf).bounds = mapWithBounds f xs hi.bounds hf.bounds := by
  unfold mapWith
  rw [bounds_mapDependentWith, bounds_mapInput, bounds_mapOutput]
  ext e <;> simp only [mapDependentWithBounds, mapDependentBounds, mapWithBounds,
    compBounds, Function.comp_apply, Nat.add_assoc, Sigma.encode_mk]


attribute [scoped fun_prop] Implementation.identity Implementation.comp Implementation.reverse
  Implementation.map Implementation.append Implementation.fst Implementation.snd
  Implementation.pair Implementation.unit Implementation.ofEncode Implementation.ite
  Implementation.foldl
attribute [scoped fun_prop] Implementation.foldlWith
  Implementation.mapDependentWith Implementation.mapWith

end Complexity.TreeProgram.Source

namespace Complexity.TreeProgram.Source.Implementation

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [UniqueEncoding Tree γ] {f : α → β} {g : α → γ}

theorem HasGrowth.ofEncode {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p) (eq : ∀ x, ⌜g x⌝ₜ = ⌜f x⌝ₜ) :
    (Implementation.ofEncode eq hf).HasGrowth t p := by
  apply HasGrowth.of_bounds _ (bounds_ofEncode _ _) h.1 h.2

theorem HasGrowth.mapInput {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p) (i : γ → α) (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    (hf.mapInput i hi).HasGrowth (t ∘ i) (p ∘ i) :=
  HasGrowth.of_bounds _ (bounds_mapInput _ _ _) (h.1.comp i) (h.2.comp i)

theorem HasGrowth.mapOutput {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p) (o : β → γ) (ho : ∀ x, ⌜o x⌝ₜ = ⌜x⌝ₜ) :
    (hf.mapOutput o ho).HasGrowth t p :=
  HasGrowth.of_bounds _ (bounds_mapOutput _ _ _) h.1 h.2

theorem HasGrowth.congr {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p) {g : α → β} (eq : f = g) :
    (hf.congr eq).HasGrowth t p := h

theorem HasGrowth.pair {hf : Implementation f} {hg : Implementation g}
    {t p u q : α → ℕ} (h : hf.HasGrowth t p) (k : hg.HasGrowth u q) :
    (hf.pair hg).HasGrowth (fun x => t x + (u x + 1))
      (fun x => max (p x) (max (q x) ⌜(f x, g x)⌝ₜ.size)) := by
  apply HasGrowth.of_bounds _ (bounds_pair _ _)
  · exact h.1.add (k.1.add (Dominated.const 1))
  · exact h.2.max (k.2.max (Dominated.refl _))

/-- The branch is chosen at runtime, with coefficients uniform across both branches. -/
theorem HasGrowth.ite {c : α → Bool} {k : α → β}
    {hc : Implementation c} {hf : Implementation f} {hk : Implementation k}
    {tc pc tf pf tk pk : α → ℕ}
    (gc : hc.HasGrowth tc pc) (gf : hf.HasGrowth tf pf) (gk : hk.HasGrowth tk pk) :
    (hc.ite hf hk).HasGrowth
      (fun x => tc x + (if c x then tf x else tk x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pk x))) := by
  apply HasGrowth.of_bounds _ (bounds_ite _ _ _)
  · exact (gc.1.add (gf.1.ite gk.1 (fun x => c x = true))).add (Dominated.const 3)
  · exact (Dominated.refl _).max (gc.2.max (gf.2.ite gk.2 (fun x => c x = true)))

theorem HasGrowth.iteProp {c : α → Prop} [DecidablePred c] {k : α → β}
    {hc : Implementation (fun x => decide (c x))} {hf : Implementation f} {hk : Implementation k}
    {tc pc tf pf tk pk : α → ℕ}
    (gc : hc.HasGrowth tc pc) (gf : hf.HasGrowth tf pf) (gk : hk.HasGrowth tk pk) :
    (hc.iteProp hf hk).HasGrowth
      (fun x => tc x + (if c x then tf x else tk x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pk x))) := by
  simpa only [Implementation.iteProp, decide_eq_true_eq] using
    (gc.ite gf gk).congr (by funext x; simp)

end Complexity.TreeProgram.Source.Implementation

namespace Complexity.TreeProgram.Source.Implementation

@[source_growth] theorem hasGrowth_reverse {α : Type*} [UniqueEncoding Tree α] :
    (reverse (α := α)).HasGrowth (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  apply HasGrowth.of_bounds _ bounds_reverse
  all_goals
    dsimp only [reverseBounds]
    simp only [Dominated.add_iff, Dominated.const_mul_left_iff, Nat.ofNat_pos]
    repeat' apply And.intro
  all_goals first
    | exact Dominated.of_le length_le_codeSize
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

@[source_growth] theorem hasGrowth_increment : increment.HasGrowth
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  apply HasGrowth.of_bounds _ bounds_increment
  · exact ((Dominated.of_le length_le_codeSize).const_mul_left _).add_same
      (Dominated.const_of_pos _ fun _ => Tree.size_pos _)
  · exact (Dominated.refl _).add_same (Dominated.const_of_pos _ fun _ => Tree.size_pos _)

/-- Primitive specifications are saved once; calls retain their original implementations. -/
@[source_growth] theorem hasGrowth_succ : succ.HasGrowth
    (fun n => ⌜n⌝ₜ.size) (fun n => ⌜n⌝ₜ.size) := by
  apply HasGrowth.of_bounds _ bounds_succ
  · have h : Dominated (fun n : ℕ => n.bits.length) (fun n => ⌜n⌝ₜ.size) :=
      Dominated.of_le fun n => length_le_codeSize n.bits
    exact (h.const_mul_left 28).add_same (Dominated.const_of_pos 25 fun _ => Tree.size_pos _)
  · exact (Dominated.refl _).add_same (Dominated.const_of_pos 5 fun _ => Tree.size_pos _)

end Complexity.TreeProgram.Source.Implementation

namespace Complexity.TreeProgram.Source

/-- Fold callbacks share one growth coefficient across all environments and reachable states.
The library charges each traversal step once and takes a peak, without multiplying space by
list length. The caller supplies only its invariant and the callback size comparisons. -/
theorem Implementation.HasGrowth.foldl_of_invariant
    {α β ρ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : β → α → β} {hf : Implementation (Function.uncurry f)}
    {t p : β × α → ℕ} (h : hf.HasGrowth t p)
    (I : ρ → List α → β → Prop) (xs : ρ → List α) (initial : ρ → β)
    (time peak : ρ → ℕ) (start : ∀ x, I x (xs x) (initial x))
    (next : ∀ x a rest acc, I x (a :: rest) acc → I x rest (f acc a))
    (hsize : Dominated
      (fun z : {z : ρ × List α × β // I z.1 z.2.1 z.2.2} => ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size)
      (fun z => peak z.1.1))
    (ht : Dominated
      (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        t (z.1.2.2.2, z.1.2.1)) (fun z => time z.1.1))
    (hp : Dominated
      (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        p (z.1.2.2.2, z.1.2.1)) (fun z => peak z.1.1)) :
    Dominated (fun x => hf.foldl.bounds.time (initial x, xs x))
      (fun x => (xs x).length * time x + (xs x).length + 1) ∧
    Dominated (fun x => hf.foldl.bounds.peak (initial x, xs x)) peak := by
  let Z := {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2}
  have hc := (h.1.comp (fun z : Z => (z.1.2.2.2, z.1.2.1))).trans ht
  have hc' := (h.2.comp (fun z : Z => (z.1.2.2.2, z.1.2.1))).trans hp
  obtain ⟨Ct, htime⟩ := dominated_iff.mp hc
  obtain ⟨Cp, hpeak⟩ := dominated_iff.mp hc'
  obtain ⟨Cs, hstate⟩ := dominated_iff.mp hsize
  have bound (x : ρ) := foldlCost_le
    (f := f) (b := fun a i => ⟨hf.bounds.time (a, i), hf.bounds.peak (a, i)⟩)
    (I x) (fun rest _ => Ct * (rest.length * time x)) ((Cs + Cp) * peak x)
    (xs x) (initial x) (start x)
    (by
      intro a rest acc hi
      have ht' := htime ⟨(x, a, rest, acc), hi⟩
      have hp' := hpeak ⟨(x, a, rest, acc), hi⟩
      have hs' := hstate ⟨(x, a :: rest, acc), hi⟩
      simp only [Function.comp_apply, Nat.nsmul_eq_mul] at ht' hp' hs'
      refine ⟨next x a rest acc hi, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.mul_add]
        omega
      · apply (show ⌜(acc, a)⌝ₜ.size ≤ ⌜(acc, a :: rest)⌝ₜ.size by
          simp only [size_encode_prod, encode_list_cons]; omega).trans
        exact hs'.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      · exact hp'.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
    (by
      intro acc hi
      have hs' := hstate ⟨(x, [], acc), hi⟩
      simp only [Nat.nsmul_eq_mul] at hs'
      exact (show ⌜acc⌝ₜ.size ≤ ⌜(acc, ([] : List α))⌝ₜ.size by
        simp only [size_encode_prod]; omega).trans hs' |>.trans
          (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  have ht' : Dominated
      (fun x => (foldlCost f (fun a i => ⟨hf.bounds.time (a, i), hf.bounds.peak (a, i)⟩)
        (initial x) (xs x)).time) (fun x => (xs x).length * time x) :=
    Dominated.of_le_mul Ct fun x => (bound x).2.1
  have hp' : Dominated
      (fun x => (foldlCost f (fun a i => ⟨hf.bounds.time (a, i), hf.bounds.peak (a, i)⟩)
        (initial x) (xs x)).peak) peak :=
    Dominated.of_le_mul (Cs + Cp) fun x => (bound x).2.2
  constructor
  · simpa only [Implementation.bounds_foldl, foldlSumBounds, Nat.mul_comm] using
      (ht'.add ((Dominated.refl _).const_mul_left 13)).add (Dominated.const 10)
  · simpa only [Implementation.bounds_foldl, foldlSumBounds, Function.comp_def] using
      (hsize.comp (fun x => ⟨(x, xs x, initial x), start x⟩)).max_same hp'

/-- A prepend fold reuses the invariant rule with one coefficient for the whole traversal. -/
theorem Implementation.HasGrowth.foldl_prepend {α : Type*} [UniqueEncoding Tree α]
    {hf : Implementation (Function.uncurry (fun acc : List α => fun x => x :: acc))}
    (h : hf.HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size)) :
    hf.foldl.HasGrowth (fun x => x.2.length + 1) (fun x => ⌜x⌝ₜ.size) := by
  have hg := h.foldl_of_invariant
    (fun x : List α × List α => fun rest acc => ⌜(acc, rest)⌝ₜ.size ≤ ⌜x⌝ₜ.size)
    Prod.snd Prod.fst (fun _ => 1) (fun x => ⌜x⌝ₜ.size) (fun _ => le_rfl)
    (by intro x a rest acc hi; simpa only [size_encode_prod, encode_list_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi)
    (Dominated.of_le fun z => z.2) (Dominated.refl _)
    (Dominated.of_le fun z => (show ⌜(z.1.2.2.2, z.1.2.1)⌝ₜ.size ≤
      ⌜(z.1.2.2.2, z.1.2.1 :: z.1.2.2.1)⌝ₜ.size by
        simp only [size_encode_prod, encode_list_cons]; omega).trans z.2)
  refine ⟨hg.1.trans ?_, hg.2⟩
  simp only [Nat.mul_one, Dominated.add_iff]
  exact ⟨⟨Dominated.of_le (fun _ => Nat.le_succ _),
    Dominated.of_le (fun _ => Nat.le_succ _)⟩,
    Dominated.const_of_pos _ (fun _ => Nat.succ_pos _)⟩

end Complexity.TreeProgram.Source

namespace Complexity.TreeProgram.Source.Implementation

/-- A dependent traversal reuses one specification for its entire callback family. -/
theorem HasGrowth.mapDependent {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} {hf : Implementation (fun x : Σ e, α e => f x.1 x.2)}
    {t p : (Σ e, α e) → ℕ} (h : hf.HasGrowth t p) :
    hf.mapDependent.HasGrowth
      (fun x : Σ e, List (α e) => (x.2.map (fun a => t ⟨x.1, a⟩)).sum + x.2.length + 1)
      (fun x : Σ e, List (α e) => max ⌜x⌝ₜ.size
        (max (⌜x.2.map (f x.1)⌝ₜ.size + 1) (x.2.foldr (fun a s => max (p ⟨x.1, a⟩) s) 0))) := by
  let u : (Σ x : Σ e, List (α e), α x.1) → Σ e, α e := fun z => ⟨z.1.1, z.2⟩
  have ht := Dominated.sum_map (fun x : Σ e, List (α e) => x.2)
    (a := fun x a => hf.bounds.time ⟨x.1, a⟩) (b := fun x a => t ⟨x.1, a⟩)
    (by simpa only [Function.comp_def, u] using h.1.comp u)
  have hp := Dominated.foldr_max (fun x : Σ e, List (α e) => x.2)
    (a := fun x a => hf.bounds.peak ⟨x.1, a⟩) (b := fun x a => p ⟨x.1, a⟩)
    (by simpa only [Function.comp_def, u] using h.2.comp u)
  apply HasGrowth.of_bounds _ (bounds_mapDependent _)
  · exact (ht.add ((Dominated.refl _).const_mul_left 27)).add (Dominated.const 17)
  · exact (Dominated.refl _).max ((Dominated.refl _).max hp)

/-- Captured traversals combine the preparation and uniform callback specifications directly. -/
theorem HasGrowth.mapDependentWith {ρ β : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [UniqueEncoding Tree β]
    {f : (e : ρ) → α e → β} {xs : (e : ρ) → List (α e)}
    {hi : Implementation (fun e => (⟨e, xs e⟩ : Σ e, List (α e)))}
    {hf : Implementation (fun p : Σ e, α e => f p.1 p.2)}
    {ti pi : ρ → ℕ} {tf pf : (Σ e, α e) → ℕ}
    (gi : hi.HasGrowth ti pi) (gf : hf.HasGrowth tf pf) :
    (hi.mapDependentWith hf).HasGrowth
      (fun e => ti e + (((xs e).map (fun a => tf ⟨e, a⟩)).sum + (xs e).length + 1))
      (fun e => max (pi e) (max ⌜(⟨e, xs e⟩ : Σ e, List (α e))⌝ₜ.size
        (max (⌜(xs e).map (f e)⌝ₜ.size + 1) ((xs e).foldr (fun a s => max (pf ⟨e, a⟩) s) 0)))) :=
  gi.comp gf.mapDependent

theorem HasGrowth.mapWith {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β} {xs : ρ → List α}
    {hi : Implementation (fun e => (e, xs e))}
    {hf : Implementation (fun p : ρ × α => f p.1 p.2)}
    {ti pi : ρ → ℕ} {tf pf : ρ × α → ℕ}
    (gi : hi.HasGrowth ti pi) (gf : hf.HasGrowth tf pf) :
    (hi.mapWith hf).HasGrowth
      (fun e => ti e + (((xs e).map (fun a => tf (e, a))).sum + (xs e).length + 1))
      (fun e => max (pi e) (max ⌜(e, xs e)⌝ₜ.size
        (max (⌜(xs e).map (f e)⌝ₜ.size + 1) ((xs e).foldr (fun a s => max (pf (e, a)) s) 0)))) := by
  simpa only [Implementation.mapWith, Function.comp_apply, Sigma.encode_mk] using
    (gi.mapOutput (fun p => (⟨p.1, p.2⟩ : Σ _ : ρ, List α))
      (fun p => @Sigma.encode_mk ρ (fun _ => List α) _ _ p.1 p.2)).mapDependentWith
      (gf.mapInput (fun p : Σ _ : ρ, α => (p.1, p.2))
        (fun p => (@Sigma.encode_mk ρ (fun _ => α) _ _ p.1 p.2).symm))

end Complexity.TreeProgram.Source.Implementation
