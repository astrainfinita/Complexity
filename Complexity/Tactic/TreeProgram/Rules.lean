/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Traversal
public import Complexity.Tactic.TreeProgram.Implementation
public import Complexity.Tactic.Hole
public import Complexity.Models.TreeMachine.Language.Nat
public import Complexity.Encoding.Sigma
public import Complexity.Encoding.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Source-function primitives and combinators

Each rule states the growth of its result in terms of the growth of its premises. Fixed
controller costs of the generated code are absorbed into the hidden coefficient.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

@[simp, dominated_simp]
theorem size_encode_reverse {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    (encode Tree xs.reverse).size = (encode Tree xs).size := by
  simpa using Tree.size_reverseAppend ⌜xs⌝ₜ ⌜([] : List α)⌝ₜ

grind_pattern size_encode_list_append => ⌜xs ++ ys⌝ₜ.size
grind_pattern size_encode_reverse => ⌜xs.reverse⌝ₜ.size

@[dominated] theorem length_le_codeSize {α : Type*} [UniqueEncoding Tree α] (xs : List α) :
    xs.length ≤ (encode Tree xs).size := by
  rw [size_encode_list]
  omega

/-- A certified linear-time reversal, without traversing the encoded elements. -/
theorem _root_.List.hasProgramIn_reverse {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.reverse : List α → List α) List.Code.reverse IsO(fun xs => ⌜xs⌝ₜ.size)
      IsO(fun xs => ⌜xs⌝ₜ.size) := HasProgramInO.toHasProgramIn <|
  ⟨⟨fun xs => 13 * xs.length + 8, fun xs => ⌜xs⌝ₜ.size + 1⟩,
    ⟨fun v n _ => by
      change n ≤ n + 8 ∧ n + 7 + 1 ≤ n + 8
      omega,
    fun v n s xs _ hx => by
      apply (List.Code.reverse_bounded v n s).mono
      · simp [hx]
      · simp [hx]
      · intro w t ⟨hw, hframe⟩
        refine ⟨?_, hframe⟩
        rw [hx] at hw
        simpa using hw.trans (reverseAppend_encode_list xs ([] : List α))⟩,
    Dominated.of_le_mul 21 fun xs => by
      dsimp only
      have := length_le_codeSize xs
      have := Tree.size_pos ⌜xs⌝ₜ
      omega,
    Dominated.of_le_mul 2 fun xs => by
      dsimp only
      have := Tree.size_pos ⌜xs⌝ₜ
      omega⟩

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
/-- Apply a primitive to the results of two programs. -/
theorem Internal.HasProgramInO.binary {α β γ δ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] [UniqueEncoding Tree γ] [UniqueEncoding Tree δ]
    {f : α → β} {g : α → γ} {op : β → γ → δ} {d : Bounds (β × γ)} {t p u q : α → ℕ}
    {pf pg : Value → Code Value} {r : Value → Value → Code Value} (hr : BinarySpec r op d)
    (hf : HasProgramInO f pf t p) (hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => op (f x) (g x)) (fun v => do let w ← pf v; let z ← pg v; r w z)
      (fun x => t x + (u x + d.time (f x, g x)))
      (fun x => max (p x) (max (q x) (d.peak (f x, g x)))) := by
  obtain ⟨b, hb, hbt, hbp⟩ := hf.sound
  obtain ⟨c, hc, hct, hcp⟩ := hg.sound
  exact ⟨_, Implements.binary hr hb hc, hbt.add (hct.add (.refl _)),
    hbp.max (hcp.max (.refl _))⟩

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

/-- Pair two computed values, whose types may depend on the input. -/
theorem Implements.pair {α : Type*} {β γ : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] [∀ x, UniqueEncoding Tree (γ x)]
    {p q : Value → Code Value} {f : (x : α) → β x} {g : (x : α) → γ x} {b c : Bounds α}
    (hf : Implements p f b) (hg : Implements q g c) :
    Implements (fun v => do let w ← p v; let z ← q v; Value.pair w z) (fun x => (f x, g x))
      ⟨fun x => b.time x + (c.time x + 1),
        fun x => max (b.peak x) (max (c.peak x) ⌜(f x, g x)⌝ₜ.size)⟩ := by
  refine hf.bind_input ?_ ?_
  · intro u v n hu hv
    obtain ⟨hn, _⟩ := hg.1 v n hv
    simp only [Code.build_bind, Value.pair, Code.eval_build]
    exact ⟨hn.trans (Nat.le_succ _), le_rfl⟩
  · intro u v n s x hu hv hux hvx
    obtain ⟨hn, hz⟩ := hg.1 v n hv
    apply Code.Bounded.bind ((hg.2 v n s x hv hvx).with_result.mono le_rfl
      (Nat.le_max_left _ _) (fun _ _ h => h))
    rintro z t ⟨rfl, hzVal, ht⟩
    have hut : u.eval t = ⌜f x⌝ₜ := (u.eval_eq_of_forall_lt hu ht).trans hux
    simp only [Value.pair, Code.bounded_eval_iff]
    refine ⟨by cases u <;> cases (q v).build n |>.1 <;> simp, ?_, ?_, ?_⟩
    · simp [hut, hzVal, encode_prod]; omega
    · simp [hut, hzVal, encode_prod]
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact ht j hj

section Pair

variable {α : Type*} {β γ : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  [∀ x, UniqueEncoding Tree (γ x)] {pf pg : Value → Code Value} {t p u q : α → ℕ}

/-- Compute two values, whose types may depend on the input, and pair their encodings. -/
theorem Internal.HasProgramInO.pair {f : (x : α) → β x} {g : (x : α) → γ x}
    (hf : HasProgramInO f pf t p) (hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => (f x, g x)) (fun v => do let w ← pf v; let z ← pg v; Value.pair w z)
      (fun x => t x + (u x + 1)) (fun x => max (p x) (max (q x) ⌜(f x, g x)⌝ₜ.size)) := by
  obtain ⟨b, hb, hbt, hbp⟩ := hf.sound
  obtain ⟨c, hc, hct, hcp⟩ := hg.sound
  exact ⟨_, hb.pair hc, hbt.add (hct.add (.refl _)), hbp.max (hcp.max (.refl _))⟩

end Pair

section Append

variable {α : Type*} {β : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  {pf pg : Value → Code Value} {t p u q : α → ℕ}

theorem encode_list_codes {γ : Type*} [UniqueEncoding Tree γ] (xs : List γ) :
    ⌜xs.map (encode Tree)⌝ₜ = ⌜xs⌝ₜ :=
  encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _) xs

theorem encode_prod_congr {γ δ γ' δ' : Type*} [UniqueEncoding Tree γ] [UniqueEncoding Tree δ]
    [UniqueEncoding Tree γ'] [UniqueEncoding Tree δ'] {a : γ} {b : δ} {a' : γ'} {b' : δ'}
    (ha : ⌜a'⌝ₜ = ⌜a⌝ₜ) (hb : ⌜b'⌝ₜ = ⌜b⌝ₜ) : ⌜(a', b')⌝ₜ = ⌜(a, b)⌝ₜ := by
  rw [encode_prod, encode_prod, ha, hb]

/-- A function with one program at every type, applied to a computed value whose type may depend
on the input: the instance on the value's codes `c` gives the growth, the one at its type the
result. -/
theorem Internal.HasProgramInO.comp_codes {A δ : α → Type*} {B γ : Type*}
    [∀ x, UniqueEncoding Tree (A x)] [∀ x, UniqueEncoding Tree (δ x)] [UniqueEncoding Tree B]
    [UniqueEncoding Tree γ]
    {F : (x : α) → A x → δ x} {G : B → γ} {f : (x : α) → A x} {program : Value → Code Value}
    {u q : B → ℕ} {u' q' : (x : α) → A x → ℕ} (hf : HasProgramInO f pf t p)
    (c : (x : α) → A x → B) (hc : ∀ x a, ⌜c x a⌝ₜ = ⌜a⌝ₜ) (hG : HasProgramInO G program u q)
    (hF : ∀ x, HasProgramInO (F x) program (u' x) (q' x)) :
    HasProgramInO (fun x => F x (f x)) (fun v => pf v >>= program) (fun x => t x + u (c x (f x)))
      (fun x => max (p x) (q (c x (f x)))) :=
  ((hf.of_encode fun x => hc x (f x)).comp_dependent hG).of_encode
    fun x => by
      obtain ⟨_, h, -⟩ := (hF x).sound
      obtain ⟨_, g, -⟩ := hG.sound
      exact h.encode_congr g (hc x (f x)).symm

theorem dominated_of_eq {ι : Type*} {f g : ι → ℕ} (h : f = g) : Dominated f g :=
  h ▸ .refl f

end Append

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

/-- A maximum over a list of maxima is the maximum of the two maxima over the list, as
`List.sum_map_add` for sums. -/
theorem foldr_max_max {α : Type*} (a b : α → ℕ) (xs : List α) :
    xs.foldr (fun x n => max (max (a x) (b x)) n) 0 =
      max (xs.foldr (fun x n => max (a x) n) 0) (xs.foldr (fun x n => max (b x) n) 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, max_max_max_comm]

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

/-- Reuse one callback for every element; time is summed and space is a peak. -/
theorem Internal.HasProgramInO.map {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {pf : Value → Code Value} {t p : α → ℕ} (hf : HasProgramInO f pf t p) :
    HasProgramInO (List.map f) (List.Code.map pf) (fun xs => (xs.map t).sum + xs.length + 1)
      (fun xs => max ⌜xs⌝ₜ.size (max (⌜xs.map f⌝ₜ.size + 1)
        (xs.foldr (fun x s => max (p x) s) 0))) := by
  obtain ⟨b, h, hbt, hbp⟩ := hf.sound
  have ht : Dominated (fun z : (_ : List α) × α => b.time z.2) (fun z => t z.2) :=
    hbt.comp _
  have hp : Dominated (fun z : (_ : List α) × α => b.peak z.2) (fun z => p z.2) :=
    hbp.comp _
  refine ⟨_, h.map, ?_, ?_⟩
  · exact ((Dominated.sum_map (fun xs : List α => xs) ht).add
      ((Dominated.refl _).const_mul_left 26)).add (Dominated.const 15)
  · change Dominated (fun xs : List α => max ⌜xs⌝ₜ.size (max (⌜xs.map f⌝ₜ.size + 1)
      (xs.foldr (fun x n => max (b.peak x) n) 0))) _
    exact (Dominated.refl _).max ((Dominated.refl _).max
      (Dominated.foldr_max (fun xs : List α => xs) hp))

/-- Map bounds for a list with a shared, possibly dependent environment. -/
@[simps] def mapDependentBounds {ρ : Type*} {α β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [∀ e, UniqueEncoding Tree (β e)]
    (f : (e : ρ) → α e → β e) (b : Bounds (Σ e, α e)) : Bounds (Σ e, List (α e)) :=
  ⟨fun x => (x.2.map (fun y => b.time ⟨x.1, y⟩)).sum + 27 * x.2.length + 17,
    fun x => max ⌜x⌝ₜ.size (max (⌜x.2.map (f x.1)⌝ₜ.size + 1)
      (x.2.foldr (fun y s => max (b.peak ⟨x.1, y⟩) s) 0))⟩

theorem Implements.map_dependent {ρ : Type*} {α β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [∀ e, UniqueEncoding Tree (β e)]
    {p : Value → Code Value} {f : (e : ρ) → α e → β e} {b : Bounds (Σ e, α e)}
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

/-- The captured environment is kept once; a single callback handles every runtime index. -/
theorem Internal.HasProgramInO.map_dependent {ρ : Type*} {α β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [∀ e, UniqueEncoding Tree (β e)]
    {f : (e : ρ) → α e → β e} {pf : Value → Code Value} {t p : (Σ e, α e) → ℕ}
    (hf : HasProgramInO (fun x : Σ e, α e => f x.1 x.2) pf t p) :
    HasProgramInO (fun x : Σ e, List (α e) => x.2.map (f x.1)) (Traversal.mapDependentProgram pf)
      (fun x => (x.2.map (fun y => t ⟨x.1, y⟩)).sum + x.2.length + 1)
      (fun x => max ⌜x⌝ₜ.size (max (⌜x.2.map (f x.1)⌝ₜ.size + 1)
        (x.2.foldr (fun y s => max (p ⟨x.1, y⟩) s) 0))) := by
  obtain ⟨b, h, hbt, hbp⟩ := hf.sound
  let u : (Σ x : Σ e, List (α e), α x.1) → Σ e, α e := fun z => ⟨z.1.1, z.2⟩
  refine ⟨_, h.map_dependent, ?_, ?_⟩
  · exact ((Dominated.sum_map (fun x : Σ e, List (α e) => x.2)
      (by simpa only [Function.comp_def, u] using hbt.comp u)).add
        ((Dominated.refl _).const_mul_left 27)).add (Dominated.const 17)
  · exact (Dominated.refl _).max ((Dominated.refl _).max
      (Dominated.foldr_max (fun x : Σ e, List (α e) => x.2)
        (by simpa only [Function.comp_def, u] using hbp.comp u)))

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
    exact ⟨by dsimp [loopCode]; omega,
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

/-- Binary successor on bit lists. -/
theorem _root_.Complexity.BitList.hasProgramIn_increment :
    HasProgramIn BitList.increment Nat.Code.succ IsO(fun xs => ⌜xs⌝ₜ.size)
      IsO(fun xs => ⌜xs⌝ₜ.size) :=
  HasProgramInO.toHasProgramIn <|
  ⟨⟨fun xs => 28 * xs.length + 25, fun xs => ⌜xs⌝ₜ.size + 5⟩,
    ⟨fun v n _ => by
      change n ≤ n + 23 ∧ n + 22 + 1 ≤ n + 23
      omega,
    fun v n s xs _ hx => Nat.Code.succ_bits_bounded v n s xs hx⟩,
    Dominated.of_le_mul 53 fun xs => by
      dsimp only
      have := length_le_codeSize xs
      have := Tree.size_pos ⌜xs⌝ₜ
      omega,
    Dominated.of_le_mul 6 fun xs => by
      dsimp only
      have := Tree.size_pos ⌜xs⌝ₜ
      omega⟩

section Constructor

variable {α : Type*} {β γ δ : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  [∀ x, UniqueEncoding Tree (γ x)] [∀ x, UniqueEncoding Tree (δ x)] {t p u q : α → ℕ}

/-- Write a constant tag before a computed value. -/
theorem Implements.tagged {pf : Value → Code Value} {f : (x : α) → β x} {b : Bounds α}
    {g : (x : α) → γ x} (T : Tree) (henc : ∀ x, ⌜g x⌝ₜ = .pair T ⌜f x⌝ₜ)
    (hf : Implements pf f b) :
    Implements (fun v => do let w ← pf v; Code.eval (.pair (.ofTree T) w.expression)) g
      ⟨fun x => b.time x + ((Expr.ofTree T : Expr ℕ).steps + 1),
        fun x => max (b.peak x) ⌜g x⌝ₜ.size⟩ := by
  refine hf.bind_input ?_ ?_
  · intro u v n _ _
    simp [Expr.bound]
  · intro u v n s x hu _ hux _
    simp only [Code.bounded_eval_iff]
    have hT : T.size < ⌜g x⌝ₜ.size := by rw [henc]; simp; omega
    have hw : (u.eval s).size < ⌜g x⌝ₜ.size := by rw [henc, hux]; simp
    refine ⟨by cases u <;> simp [Expr.assignSteps], ?_, by simp [hux, henc], fun j hj => ?_⟩
    · simp only [Expr.maxSize, Expr.maxSize_ofTree, Expr.eval_ofTree, Value.maxSize_expression,
        Value.eval_expression]
      have : (Tree.pair T (u.eval s)).size = ⌜g x⌝ₜ.size := by rw [henc, hux]
      omega
    · rw [Function.update_of_ne (by omega)]

/-- The last field of a constructor, with its size counted in its peak. -/
theorem Internal.HasProgramInO.with_size {f : (x : α) → β x} {pf : Value → Code Value}
    (hf : HasProgramInO f pf t p) : HasProgramInO f pf t (fun x => max (p x) ⌜f x⌝ₜ.size) :=
  hf.mono (.refl _) (Dominated.of_le fun _ => le_max_left _ _)

/-- Compute a field before the remaining fields of a constructor; the tuple is counted once. -/
theorem Internal.HasProgramInO.field_cons {f : (x : α) → β x} {g : (x : α) → γ x}
    {pf pg : Value → Code Value} (hf : HasProgramInO f pf t p)
    (hg : HasProgramInO g pg u (fun x => max (q x) ⌜g x⌝ₜ.size)) :
    HasProgramInO (fun x => (f x, g x)) (fun v => do let w ← pf v; let z ← pg v; Value.pair w z)
      (fun x => t x + (u x + 1)) (fun x => max (max (p x) (q x)) ⌜(f x, g x)⌝ₜ.size) :=
  (hf.pair hg).mono (.refl _) (Dominated.of_le fun x => by simp only [size_encode_prod]; omega)

/-- A constructor whose code is the tuple of its fields. -/
theorem Internal.HasProgramInO.of_fields {f : (x : α) → β x} {g : (x : α) → γ x}
    {pf : Value → Code Value}
    (henc : ∀ x, ⌜g x⌝ₜ = ⌜f x⌝ₜ) (hf : HasProgramInO f pf t (fun x => max (p x) ⌜f x⌝ₜ.size)) :
    HasProgramInO g pf t (fun x => max (p x) ⌜g x⌝ₜ.size) :=
  (hf.of_encode henc).mono (.refl _) (Dominated.of_le fun x => by rw [henc])

/-- A constructor whose code is a constant tag paired with the tuple of its fields. -/
theorem Internal.HasProgramInO.of_tagged_fields {f : (x : α) → β x} {g : (x : α) → γ x}
    {pf : Value → Code Value} (T : Tree) (henc : ∀ x, ⌜g x⌝ₜ = .pair T ⌜f x⌝ₜ)
    (hf : HasProgramInO f pf t (fun x => max (p x) ⌜f x⌝ₜ.size)) :
    HasProgramInO g (fun v => do let w ← pf v; Code.eval (.pair (.ofTree T) w.expression))
      (fun x => t x + 1) (fun x => max (p x) ⌜g x⌝ₜ.size) := by
  obtain ⟨b, hb, hbt, hbp⟩ := hf.sound
  refine ⟨_, Implements.tagged T henc hb, ?_, ?_⟩
  · exact (hbt.trans (Dominated.of_le fun _ => Nat.le_succ _)).add_same
      (Dominated.const_of_pos _ fun _ => Nat.succ_pos _)
  · refine (hbp.max (Dominated.refl _)).trans (Dominated.of_le fun x => ?_)
    have : ⌜f x⌝ₜ.size < ⌜g x⌝ₜ.size := by rw [henc]; simp only [Tree.size_pair]; omega
    simp only [max_le_iff]
    exact ⟨⟨le_max_left _ _, this.le.trans (le_max_right _ _)⟩, le_max_right _ _⟩

end Constructor

section Projection

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]

/-- Select the index of an encoded dependent pair. -/
theorem _root_.Sigma.hasProgramIn_fst {γ : Type*} {δ : γ → Type*} [UniqueEncoding Tree γ]
    [∀ a, UniqueEncoding Tree (δ a)] :
    HasProgramIn (fun x : Σ a, δ a => x.1) Value.left IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) :=
  HasProgramInO.toHasProgramIn <| .of_implements ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩ ⟨fun v n hv => by
      change n ≤ n + 1 ∧ n + 1 ≤ n + 1
      omega,
    fun v n s ⟨x, y⟩ hv hx => by simp +contextual (disch := omega) [hx, Sigma.encode_mk]⟩

/-- Select the value of an encoded dependent pair. -/
theorem _root_.Sigma.hasProgramIn_snd {γ : Type*} {δ : γ → Type*} [UniqueEncoding Tree γ]
    [∀ a, UniqueEncoding Tree (δ a)] :
    HasProgramIn (fun x : Σ a, δ a => x.2) Value.right IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) :=
  HasProgramInO.toHasProgramIn <| .of_implements ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩ ⟨fun v n hv => by
      change n ≤ n + 1 ∧ n + 1 ≤ n + 1
      omega,
    fun v n s ⟨x, y⟩ hv hx => by simp +contextual (disch := omega) [hx, Sigma.encode_mk]⟩

/-- Select the first field of an encoded pair, which is encoded as a dependent pair. -/
theorem _root_.Prod.hasProgramIn_fst :
    HasProgramIn (Prod.fst : α × β → α) Value.left IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) :=
  HasProgramInO.toHasProgramIn <|
    (Sigma.hasProgramIn_fst (δ := fun _ => β)).toHasProgramInO.map_input
      (fun x : α × β => ⟨x.1, x.2⟩) fun x => @Sigma.encode_mk α (fun _ => β) _ _ x.1 x.2

/-- Select the second field of an encoded pair, which is encoded as a dependent pair. -/
theorem _root_.Prod.hasProgramIn_snd :
    HasProgramIn (Prod.snd : α × β → β) Value.right IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) :=
  HasProgramInO.toHasProgramIn <|
    (Sigma.hasProgramIn_snd (δ := fun _ => β)).toHasProgramInO.map_input
      (fun x : α × β => ⟨x.1, x.2⟩) fun x => @Sigma.encode_mk α (fun _ => β) _ _ x.1 x.2

-- The same implementation works for different result types when their encoded outputs coincide.
/-- Return the empty tree representing unit without allocating a register. -/
theorem Internal.HasProgramInO.unit :
    HasProgramInO (fun _ : α => ()) (fun _ => pure .nil) (fun _ => 0) (fun _ => 0) :=
  .of_implements ⟨fun _ => 0, fun _ => 0⟩ ⟨fun v n hv =>
      ⟨le_rfl, Nat.zero_le _⟩,
    fun v n s x hv hx => by simp [encode_unit]⟩

end Projection

/-- Append two lists, traversing the first. -/
theorem _root_.List.hasProgramIn_append {γ : Type*} [UniqueEncoding Tree γ] :
    HasProgramIn (fun p : List γ × List γ => p.1 ++ p.2)
      (fun v => do let w ← Value.left v; let z ← Value.right v; List.Code.append w z)
      IsO(fun p => p.1.length + 1) IsO(fun p => ⌜p⌝ₜ.size) := HasProgramInO.toHasProgramIn <|
  (HasProgramInO.binary append_spec Prod.hasProgramIn_fst.toHasProgramInO
    Prod.hasProgramIn_snd.toHasProgramInO).mono
    (Dominated.of_le_mul 42 fun p => by dsimp only; omega)
    (Dominated.of_le fun p => by rcases p; dsimp only; simp only [size_encode_prod]; omega)

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
  apply (Implements.binary (branch_spec ht hf) hc Implements.id).mono
  intro x
  have hs := hc.size_le x
  simp only [iteBounds, id_eq, Nat.zero_add, Nat.zero_max]
  exact ⟨by omega, by omega⟩

section Branch

variable {α : Type*} {β : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  {f g : (x : α) → β x} {qc qt qf : Value → Code Value} {tc pc tf pf tg pg : α → ℕ}

/-- Evaluate the condition once and only the selected branch; coefficients cover both branches. -/
theorem Internal.HasProgramInO.ite {c : α → Bool} (hc : HasProgramInO c qc tc pc)
    (ht : HasProgramInO f qt tf pf) (hf : HasProgramInO g qf tg pg) :
    HasProgramInO (fun x => if c x then f x else g x)
      (fun v => do let test ← qc v; Bool.Code.matchOn test (qf v) (qt v))
      (fun x => tc x + (if c x then tf x else tg x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pg x))) := by
  obtain ⟨bc, hbc, hct, hcp⟩ := hc.sound
  obtain ⟨bt, hbt, htt, htp⟩ := ht.sound
  obtain ⟨bf, hbf, hft, hfp⟩ := hf.sound
  -- The branches are selected on their codes, whose type does not depend on the input.
  have h := hbc.ite
    (hbt.of_encode fun _ => Tree.encode_self _) (hbf.of_encode fun _ => Tree.encode_self _)
  exact ⟨_, h.of_encode fun x => by cases c x <;> simp only [Tree.encode_self, Bool.false_eq_true,
      ite_true, ite_false],
    (hct.add (htt.ite hft (fun x => c x = true))).add (Dominated.const 3),
    (Dominated.refl _).max (hcp.max (htp.ite hfp (fun x => c x = true)))⟩

/-- Ordinary decidable conditions share the Boolean branch program. -/
theorem Internal.HasProgramInO.ite_prop {c : α → Prop} [DecidablePred c]
    (hc : HasProgramInO (fun x => decide (c x)) qc tc pc)
    (ht : HasProgramInO f qt tf pf) (hf : HasProgramInO g qf tg pg) :
    HasProgramInO (fun x => if c x then f x else g x)
      (fun v => do let test ← qc v; Bool.Code.matchOn test (qf v) (qt v))
      (fun x => tc x + (if c x then tf x else tg x) + 1)
      (fun x => max ⌜x⌝ₜ.size (max (pc x) (if c x then pf x else pg x))) :=
  ((hc.ite ht hf).congr (by funext x; simp)).mono
    (Dominated.of_le fun x => by simp) (Dominated.of_le fun x => by simp)

end Branch

attribute [scoped fun_prop] HasProgramInO.ite_prop

/-- Captured source values travel with the accumulator in one fixed program. -/
theorem Internal.HasProgramInO.foldl_with {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → β → α → β} {a : ρ → β} {xs : ρ → List α} {qi qs : Value → Code Value}
    {ti pi : ρ → ℕ} {ts ps : ρ × β × α → ℕ}
    (hi : HasProgramInO (fun e => ((e, a e), xs e)) qi ti pi)
    (hs : HasProgramInO (fun p : ρ × β × α => f p.1 p.2.1 p.2.2) qs ts ps) :
    HasProgramInO (fun e => (xs e).foldl (f e) (a e)) hole(qi, qs ⊢ program)
      (fun e => ti e + (foldlTime (f e) (fun z => ts (e, z.1, z.2)) (a e) (xs e) +
        (xs e).length + 1))
      (fun e => max (pi e) (max ⌜((e, a e), xs e)⌝ₜ.size (⌜e⌝ₜ.size + 1 +
        foldlPeak (f e) (fun z => max ⌜((e, z.1), z.2)⌝ₜ.size (ps (e, z.1, z.2)))
          (a e) (xs e)))) := by
  have hargs (z : (ρ × β) × α) : ⌜(z.1.1, z.1.2, z.2)⌝ₜ.size = ⌜z⌝ₜ.size := by
    rcases z with ⟨⟨e, a⟩, x⟩
    simp only [size_encode_prod]; omega
  have hout := hs.size_encode.comp (fun z : (ρ × β) × α => (z.1.1, z.1.2, z.2))
  simp only [Function.comp_def, hargs] at hout
  have getEnv := ((Prod.hasProgramIn_fst (β := α)).toHasProgramInO).comp
    ((Prod.hasProgramIn_fst (α := ρ) (β := β)).toHasProgramInO)
  have getArgs := getEnv.pair ((Prod.hasProgramIn_fst.toHasProgramInO.comp
    Prod.hasProgramIn_snd.toHasProgramInO).pair
    Prod.hasProgramIn_snd.toHasProgramInO)
  have step : HasProgramInO (Function.uncurry (fun (ea : ρ × β) (x : α) => (ea.1, f ea.1 ea.2 x)))
      _ (fun z => ts (z.1.1, z.1.2, z.2) + 1)
      (fun z => max ⌜z⌝ₜ.size (ps (z.1.1, z.1.2, z.2))) :=
    (getEnv.pair (getArgs.comp hs)).mono
      (Dominated.of_le_mul 10 fun z => by simp only [Function.comp_apply]; omega)
      (by
        simp only [Dominated.max_iff, Dominated.add_iff, size_encode_prod, Function.comp_apply]
        repeat' apply And.intro
        all_goals first
          | exact hout
          | exact Dominated.const_of_pos _ fun z => (Tree.size_pos _).trans_le (le_max_left _ _)
          | exact Dominated.of_le fun z => le_max_right _ _
          | exact Dominated.of_le fun z => (show _ ≤ ⌜z⌝ₜ.size by
              rcases z with ⟨⟨e, a⟩, x⟩; simp only [size_encode_prod]; omega).trans
                (le_max_left _ _))
  fill_hole program in
    refine ((hi.comp (step.foldl.comp Prod.hasProgramIn_snd.toHasProgramInO)).congr ?_).mono ?_ ?_
  · funext e
    have hfold : (xs e).foldl (fun (ea : ρ × β) x => (ea.1, f ea.1 ea.2 x)) (e, a e) =
        (e, (xs e).foldl (f e) (a e)) := List.foldl_hom (fun b => (e, b)) (by intros; rfl)
    simpa only [Function.comp_def] using congrArg Prod.snd hfold
  · apply Dominated.of_le_mul 2
    intro e
    simp only [foldlTime_add_one, foldlTime_lift]
    omega
  · apply Dominated.of_le_mul 3
    intro e
    have hlift := foldlPeak_lift_le f (fun z => max ⌜z⌝ₜ.size (ps (z.1.1, z.1.2, z.2)))
      e (a e) (xs e)
    have hres := size_foldl_le_foldlPeak (f := fun (ea : ρ × β) x => (ea.1, f ea.1 ea.2 x))
      (fun z => max ⌜z⌝ₜ.size (ps (z.1.1, z.1.2, z.2))) (e, a e) (xs e)
    simp only [max_le_iff] at hlift hres ⊢
    omega

/-- The input-producing program and uniform callback compose without choosing new code. -/
theorem Internal.HasProgramInO.map_dependent_with {ρ : Type*} {α β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)] [∀ e, UniqueEncoding Tree (β e)]
    {f : (e : ρ) → α e → β e} {xs : (e : ρ) → List (α e)} {qi qf : Value → Code Value}
    {ti pi : ρ → ℕ} {tf pf : (Σ e, α e) → ℕ}
    (hi : HasProgramInO (fun e => (⟨e, xs e⟩ : Σ e, List (α e))) qi ti pi)
    (hf : HasProgramInO (fun p : Σ e, α e => f p.1 p.2) qf tf pf) :
    HasProgramInO (fun e => (xs e).map (f e)) (fun v => qi v >>= Traversal.mapDependentProgram qf)
      (fun e => ti e + (((xs e).map (fun y => tf ⟨e, y⟩)).sum + (xs e).length + 1))
      (fun e => max (pi e) (max ⌜(⟨e, xs e⟩ : Σ e, List (α e))⌝ₜ.size
        (max (⌜(xs e).map (f e)⌝ₜ.size + 1) ((xs e).foldr (fun y s => max (pf ⟨e, y⟩) s) 0)))) :=
  hi.comp_dependent hf.map_dependent

/-- The constant-family specialization of a captured map. Callbacks that capture an environment of
a fixed type are stated on `ρ × α`; through `map_dependent_with` alone they would be stated on
`Σ _ : ρ, α`, and a hypothesis on `ρ × α` is found only after an extra composition. -/
theorem Internal.HasProgramInO.map_with {ρ α β : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : ρ → α → β} {xs : ρ → List α} {qi qf : Value → Code Value} {ti pi : ρ → ℕ}
    {tf pf : ρ × α → ℕ} (hi : HasProgramInO (fun e => (e, xs e)) qi ti pi)
    (hf : HasProgramInO (fun p : ρ × α => f p.1 p.2) qf tf pf) :
    HasProgramInO (fun e => (xs e).map (f e)) (fun v => qi v >>= Traversal.mapDependentProgram qf)
      (fun e => ti e + (((xs e).map (fun y => tf (e, y))).sum + (xs e).length + 1))
      (fun e => max (pi e) (max ⌜(e, xs e)⌝ₜ.size
        (max (⌜(xs e).map (f e)⌝ₜ.size + 1) ((xs e).foldr (fun y s => max (pf (e, y)) s) 0)))) :=
  (HasProgramInO.map_dependent_with
    (hi.of_encode (fun e => @Sigma.encode_mk ρ (fun _ => List α) _ _ e (xs e)))
    (hf.map_input (fun p : Σ _ : ρ, α => (p.1, p.2))
      (fun p => (@Sigma.encode_mk ρ (fun _ => α) _ _ p.1 p.2).symm))).mono
    (Dominated.refl _) (Dominated.of_le fun e => by simp only [Sigma.encode_mk, le_refl])

attribute [scoped fun_prop] HasProgramInO.identity HasProgramInO.comp HasProgramInO.map
  HasProgramInO.pair HasProgramInO.unit HasProgramInO.ite HasProgramInO.foldl
attribute [scoped fun_prop] HasProgramInO.foldl_with
  HasProgramInO.map_dependent_with HasProgramInO.map_with

/-- Fold callbacks share one coefficient across all environments and reachable states.
Time is charged per element and space is a peak, not multiplied by the list length. -/
theorem Dominated.foldl_of_invariant {α β ρ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] {f : ρ → β → α → β} {t p : ρ → β × α → ℕ}
    (I : ρ → List α → β → Prop) (xs : ρ → List α) (initial : ρ → β)
    (time peak : ρ → ℕ) (start : ∀ x, I x (xs x) (initial x))
    (next : ∀ x a rest acc, I x (a :: rest) acc → I x rest (f x acc a))
    (hsize : Dominated
      (fun z : {z : ρ × List α × β // I z.1 z.2.1 z.2.2} => ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size)
      (fun z => peak z.1.1))
    (ht : Dominated
      (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        t z.1.1 (z.1.2.2.2, z.1.2.1)) (fun z => time z.1.1))
    (hp : Dominated
      (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        p z.1.1 (z.1.2.2.2, z.1.2.1)) (fun z => peak z.1.1)) :
    Dominated (fun x => foldlTime (f x) (t x) (initial x) (xs x))
      (fun x => (xs x).length * time x) ∧
    Dominated (fun x => max ⌜(initial x, xs x)⌝ₜ.size (foldlPeak (f x) (p x) (initial x) (xs x)))
      peak := by
  obtain ⟨Ct, htime⟩ := dominated_iff.mp ht
  obtain ⟨Cp, hpeak⟩ := dominated_iff.mp hp
  obtain ⟨Cs, hstate⟩ := dominated_iff.mp hsize
  have bound (x : ρ) := foldl_le_of_invariant (f := f x) (t := t x) (p := p x)
    (I x) (fun rest _ => Ct * (rest.length * time x)) ((Cs + Cp) * peak x)
    (xs x) (initial x) (start x)
    (by
      intro a rest acc hi
      have ht' := htime ⟨(x, a, rest, acc), hi⟩
      have hp' := hpeak ⟨(x, a, rest, acc), hi⟩
      have hs' := hstate ⟨(x, a :: rest, acc), hi⟩
      simp only [Nat.nsmul_eq_mul] at ht' hp' hs'
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
  refine ⟨Dominated.of_le_mul Ct fun x => (bound x).2.1, ?_⟩
  exact (hsize.comp (fun x => ⟨(x, xs x, initial x), start x⟩)).max_same
    (Dominated.of_le_mul (Cs + Cp) fun x => (bound x).2.2)

/-- A fold whose stored states and callbacks are polynomial over an invariant family, uniformly in
a scale of the environment, is polynomial in that scale. -/
theorem IsPoly.foldl_of_invariant {α β ρ : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] {f : ρ → β → α → β} {t p : ρ → β × α → ℕ}
    (I : ρ → List α → β → Prop) (xs : ρ → List α) (initial : ρ → β) (S : ρ → ℕ)
    (start : ∀ x, I x (xs x) (initial x))
    (next : ∀ x a rest acc, I x (a :: rest) acc → I x rest (f x acc a))
    (hsize : IsPoly (fun z : {z : ρ × List α × β // I z.1 z.2.1 z.2.2} => S z.1.1)
      fun z => ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size)
    (ht : IsPoly (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
      S z.1.1) fun z => t z.1.1 (z.1.2.2.2, z.1.2.1))
    (hp : IsPoly (fun z : {z : ρ × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
      S z.1.1) fun z => p z.1.1 (z.1.2.2.2, z.1.2.1)) :
    IsPoly S (fun x => foldlTime (f x) (t x) (initial x) (xs x)) ∧
      IsPoly S (fun x => foldlPeak (f x) (p x) (initial x) (xs x)) := by
  have hlen : IsPoly S fun x => (xs x).length :=
    (hsize.comp (h := fun x => ⟨(x, xs x, initial x), start x⟩) IsPoly.refl).of_dominated
      (Dominated.of_le fun x => (length_le_codeSize _).trans (by
        simp only [size_encode_prod]; omega))
  obtain ⟨d₁, h₁⟩ := hsize
  obtain ⟨d₂, h₂⟩ := ht
  obtain ⟨d₃, h₃⟩ := hp
  let D := d₁ + d₂ + d₃
  have lift {γ : Type _} {s t : γ → ℕ} {d : ℕ} (h : Dominated t fun x => (s x + 1) ^ d)
      (hd : d ≤ D) : Dominated t fun x => (s x + 1) ^ D :=
    h.mono_pow hd fun _ => Nat.succ_pos _
  have h := Dominated.foldl_of_invariant (f := f) (t := t) (p := p) I xs initial
    (fun x => (S x + 1) ^ D) (fun x => (S x + 1) ^ D) start next
    (lift h₁ (by omega)) (lift h₂ (by omega)) (lift h₃ (by omega))
  have hD : IsPoly S fun x => (S x + 1) ^ D := (IsPoly.refl.add (.const 1)).pow D
  exact ⟨(hlen.mul hD).of_dominated h.1,
    hD.of_dominated (h.2.mono_left fun _ => le_max_right _ _)⟩

section Prefix

variable {ε α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {s : ε → ℕ}
  {f : ε → β → α → β} {a : ε → β} {xs : ε → List α}

/-- A fold is polynomial in a measure `s` of its input when its callbacks are polynomial in `s` and
the codes of their arguments, the states it reaches after every prefix of its list are polynomial
in `s`, and so is its list. The invariant is that the state is the fold of the prefix consumed. -/
theorem IsPoly.foldl_of_prefix {t p : ε → β × α → ℕ}
    (ht : IsPoly (fun z : ε × (β × α) => s z.1 + ⌜z.2⌝ₜ.size) fun z => t z.1 z.2)
    (hp : IsPoly (fun z : ε × (β × α) => s z.1 + ⌜z.2⌝ₜ.size) fun z => p z.1 z.2)
    (hacc : IsPoly (fun z : {z : ε × List α // z.2 <+: xs z.1} => s z.1.1)
      fun z => ⌜z.1.2.foldl (f z.1.1) (a z.1.1)⌝ₜ.size)
    (hxs : IsPoly s fun x => ⌜xs x⌝ₜ.size) :
    IsPoly s (fun x => foldlTime (f x) (t x) (a x) (xs x)) ∧
      IsPoly s (fun x => foldlPeak (f x) (p x) (a x) (xs x)) := by
  let I x rest acc := ∃ ys, ys ++ rest = xs x ∧ ys.foldl (f x) (a x) = acc
  have hstate : IsPoly (fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} => s z.1.1)
      fun z => ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size := by
    have hb := hacc.comp (h := fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} =>
      ⟨(z.1.1, z.2.choose), _, z.2.choose_spec.1⟩) IsPoly.refl
    have hr := (hxs.comp (h := fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} => z.1.1)
      IsPoly.refl).of_dominated (f := fun z => ⌜z.1.2.1⌝ₜ.size) (Dominated.of_le fun z =>
        (List.suffix_append _ _).sublist.size_encode_le.trans_eq (by rw [z.2.choose_spec.1]))
    refine (((IsPoly.const 1).add hb).add hr).of_dominated (Dominated.of_le fun z => ?_)
    simp only [size_encode_prod, z.2.choose_spec.2, le_refl]
  let step (z : {z : ε × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2}) :
      ε × (β × α) := (z.1.1, (z.1.2.2.2, z.1.2.1))
  have hstep : IsPoly (fun z => s z.1.1) fun z => s (step z).1 + ⌜(step z).2⌝ₜ.size :=
    IsPoly.refl.add ((hstate.comp (h := fun z : {z : ε × α × List α × β //
      I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} => ⟨(z.1.1, z.1.2.1 :: z.1.2.2.1, z.1.2.2.2), z.2⟩)
      IsPoly.refl).of_dominated (Dominated.of_le fun z => by
        simp only [step, size_encode_prod, encode_list_cons]; omega))
  exact IsPoly.foldl_of_invariant I xs a s (fun _ => ⟨[], rfl, rfl⟩)
    (fun x u rest acc ⟨ys, h, hb⟩ => ⟨ys ++ [u], by simp [← h], by simp [hb]⟩) hstate
    (ht.comp hstep) (hp.comp hstep)

/-- The time of `IsPoly.foldl_of_prefix`, for a goal about the time alone. The premises come in
the order `dominated` tries them, the states after the prefixes first: they fail when no bound is
known. -/
@[dominated_traversal] theorem IsPoly.foldlTime {t : ε → β × α → ℕ}
    (hacc : IsPoly (fun z : {z : ε × List α // z.2 <+: xs z.1} => s z.1.1)
      fun z => ⌜z.1.2.foldl (f z.1.1) (a z.1.1)⌝ₜ.size)
    (hxs : IsPoly s fun x => ⌜xs x⌝ₜ.size)
    (ht : IsPoly (fun z : ε × (β × α) => s z.1 + ⌜z.2⌝ₜ.size) fun z => t z.1 z.2) :
    IsPoly s fun x => foldlTime (f x) (t x) (a x) (xs x) :=
  (IsPoly.foldl_of_prefix (p := fun _ _ => 0) ht (.const 0) hacc hxs).1

/-- The peak of `IsPoly.foldl_of_prefix`, for a goal about the peak alone, with the premises of
`IsPoly.foldlTime`. -/
@[dominated_traversal] theorem IsPoly.foldlPeak {p : ε → β × α → ℕ}
    (hacc : IsPoly (fun z : {z : ε × List α // z.2 <+: xs z.1} => s z.1.1)
      fun z => ⌜z.1.2.foldl (f z.1.1) (a z.1.1)⌝ₜ.size)
    (hxs : IsPoly s fun x => ⌜xs x⌝ₜ.size)
    (hp : IsPoly (fun z : ε × (β × α) => s z.1 + ⌜z.2⌝ₜ.size) fun z => p z.1 z.2) :
    IsPoly s fun x => foldlPeak (f x) (p x) (a x) (xs x) :=
  (IsPoly.foldl_of_prefix (t := fun _ _ => 0) (.const 0) hp hacc hxs).2

/-- The peak of a fold is linear in a measure `s` of its input when the peak of its callback is
linear in `s` and the code of its argument, and the states it reaches after every prefix of its
list, and the list, are linear in `s`. A peak is a maximum, so nested folds keep it linear. -/
@[dominated_traversal] theorem Dominated.foldlPeak_of_prefix {p : ε → β × α → ℕ}
    (hacc : Dominated (fun z : {z : ε × List α // z.2 <+: xs z.1} =>
      ⌜z.1.2.foldl (f z.1.1) (a z.1.1)⌝ₜ.size) fun z => s z.1.1)
    (hxs : Dominated (fun x => ⌜xs x⌝ₜ.size) s)
    (hp : Dominated (fun z : ε × (β × α) => p z.1 z.2) fun z => s z.1 + ⌜z.2⌝ₜ.size) :
    Dominated (fun x => foldlPeak (f x) (p x) (a x) (xs x)) s := by
  let I x rest acc := ∃ ys, ys ++ rest = xs x ∧ ys.foldl (f x) (a x) = acc
  have hstate : Dominated (fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} =>
      ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size) fun z => s z.1.1 := by
    have hb := hacc.comp fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} =>
      ⟨(z.1.1, z.2.choose), _, z.2.choose_spec.1⟩
    have hr := hxs.comp fun z : {z : ε × List α × β // I z.1 z.2.1 z.2.2} => z.1.1
    refine ((hb.add_same hr).add_same hr).mono_left fun z => ?_
    have hrest := (List.suffix_append z.2.choose z.1.2.1).sublist.size_encode_le
    rw [z.2.choose_spec.1] at hrest
    have := Tree.size_pos ⌜xs z.1.1⌝ₜ
    simp only [Function.comp_apply, size_encode_prod, z.2.choose_spec.2]
    omega
  have hstep : Dominated (fun z : {z : ε × α × List α × β //
      I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} => s z.1.1 + ⌜(z.1.2.2.2, z.1.2.1)⌝ₜ.size)
      fun z => s z.1.1 :=
    (Dominated.refl _).add_same ((hstate.comp fun z : {z : ε × α × List α × β //
      I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        ⟨(z.1.1, z.1.2.1 :: z.1.2.2.1, z.1.2.2.2), z.2⟩).mono_left
      fun z => by simp only [Function.comp_apply, size_encode_prod, encode_list_cons]; omega)
  exact (Dominated.foldl_of_invariant (t := fun _ _ => 0) I xs a (fun _ => 0) s
    (fun _ => ⟨[], rfl, rfl⟩)
    (fun x u rest acc ⟨ys, h, hb⟩ => ⟨ys ++ [u], by simp [← h], by simp [hb]⟩) hstate
    (Dominated.of_le fun _ => le_rfl)
    ((hp.comp fun z : {z : ε × α × List α × β // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
      (z.1.1, (z.1.2.2.2, z.1.2.1))).trans hstep)).2.mono_left fun _ => le_max_right _ _

omit [UniqueEncoding Tree β] in
/-- The time of a fold is within `g` when its list's code is and the time of each callback is
linear in the code of its element, whatever the state. Times that also grow with the state or the
environment add up to a product with the length, so they are not covered. -/
@[dominated_traversal] theorem Dominated.foldlTime_of_size_encode {t : ε → β × α → ℕ} {g : ε → ℕ}
    (hxs : Dominated (fun x => ⌜xs x⌝ₜ.size) g)
    (ht : Dominated (fun z : ε × (β × α) => t z.1 z.2) fun z => ⌜z.2.2⌝ₜ.size) :
    Dominated (fun x => foldlTime (f x) (t x) (a x) (xs x)) g := by
  obtain ⟨C, hC⟩ := dominated_iff.mp ht
  refine (Dominated.of_le_mul C fun x => ?_).trans hxs
  have h := foldlTime_le_sum (f := f x) (fun y => C * ⌜y⌝ₜ.size)
    (fun z => by simpa only [smul_eq_mul] using hC (x, z)) (a x) (xs x)
  rw [List.sum_map_mul_left] at h
  exact h.trans (Nat.mul_le_mul_left C (by rw [size_encode_list (xs x)]; omega))

end Prefix

section Map

variable {ε α β : Type*} [UniqueEncoding Tree β] {xs : ε → List α} {f : ε → α → β}

/-- The code of a mapped list is polynomial in a measure `s` of its input when the list's length
is, and so are the codes of the images of the elements that occur. -/
@[dominated_traversal] theorem IsPoly.size_encode_map {s : ε → ℕ}
    (hn : IsPoly s fun x => (xs x).length)
    (h : IsPoly (fun z : {p : ε × α // p.2 ∈ xs p.1} => s z.1.1) fun z => ⌜f z.1.1 z.1.2⌝ₜ.size) :
    IsPoly s fun x => ⌜(xs x).map (f x)⌝ₜ.size := by
  simpa only [size_encode_list, List.map_map, Function.comp_def, List.length_map] using
    ((IsPoly.list_sum (a := fun x y => ⌜f x y⌝ₜ.size) hn h).add hn).add (.const 1)

variable [UniqueEncoding Tree α]

/-- A sum over a list is within `g` when the list's code is and the summand of each element that
occurs is linear in the element's code. Summands that also grow with the environment add up to a
product with the length, so they are not covered. -/
@[dominated_traversal] theorem Dominated.list_sum_of_size_encode {a : ε → α → ℕ} {g : ε → ℕ}
    (hxs : Dominated (fun x => ⌜xs x⌝ₜ.size) g)
    (h : Dominated (fun z : {p : ε × α // p.2 ∈ xs p.1} => a z.1.1 z.1.2) fun z => ⌜z.1.2⌝ₜ.size) :
    Dominated (fun x => ((xs x).map (a x)).sum) g :=
  ((Dominated.list_sum xs a (fun _ y => ⌜y⌝ₜ.size) h).trans
    (Dominated.of_le fun x => by rw [size_encode_list (xs x)]; omega)).trans hxs

/-- The code of a mapped list is within `g` when the list's code is and the code of the image of
each element that occurs is linear in the element's code. -/
@[dominated_traversal] theorem Dominated.size_encode_map {g : ε → ℕ}
    (hxs : Dominated (fun x => ⌜xs x⌝ₜ.size) g)
    (h : Dominated (fun z : {p : ε × α // p.2 ∈ xs p.1} => ⌜f z.1.1 z.1.2⌝ₜ.size)
      fun z => ⌜z.1.2⌝ₜ.size) :
    Dominated (fun x => ⌜(xs x).map (f x)⌝ₜ.size) g := by
  refine (((Dominated.list_sum_of_size_encode (a := fun x y => ⌜f x y⌝ₜ.size) (.refl _) h).add_same
    (.refl _)).mono_left fun x => ?_).trans hxs
  simp only [size_encode_list, List.map_map, Function.comp_def, List.length_map]
  omega

end Map

end Complexity.TreeProgram.Source
