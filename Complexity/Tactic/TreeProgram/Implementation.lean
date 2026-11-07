/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Complexity.Models.TreeMachine.Language.Bounds
public import Complexity.Encoding.Prod
public import Complexity.Tactic.TreeProgram.Attributes
public import Complexity.Tactic.Dominated.Attr
public import Mathlib.Tactic.FunProp

/-! # Certified implementations of source functions

`Implements` fixes one program and certifies its result, time and intermediate-tree peak with
exact budgets. Implementations are stated as `HasProgramIn f program time peak`: some exact budgets
have growths satisfying the properties `time` and `peak`, such as `IsO(T)` or `IsPoly s`.
`Internal.HasProgramInO f program time peak`, the form the translation composes, is
`HasProgramIn` at `IsO(time)` and `IsO(peak)`: one hidden coefficient covers every input, while
sums, maxima and local constants of `time` and `peak` stay visible. Each rule states the program
and the growth it produces, so a selected program carries exactly one specification and calls
reuse it directly.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

open TreeProgram

/-- A positive cost paid from a potential drop leaves the rest of the potential for later
rounds; a drop that is not real would make the cost zero. -/
theorem add_mul_le_mul_of_le_mul_tsub {a C P Q : ℕ} (ha : 0 < a) (h : a ≤ C * (P - Q)) :
    a + C * Q ≤ C * P := by
  have hQ : Q ≤ P := by
    by_contra hn
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.mul_zero] at h
    omega
  have := Nat.mul_add C (P - Q) Q
  rw [Nat.sub_add_cancel hQ] at this
  omega

/-- Input-dependent allowances for time and intermediate-tree size. -/
@[ext] structure Bounds (α : Type*) where
  /-- Time allowance for each source input. -/
  time : α → ℕ
  /-- Intermediate-tree size allowance for each source input. -/
  peak : α → ℕ

/-- One uniform program implements the function on every encoded input, preserving its context.
The type of the result may depend on the input. -/
def Implements {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] (p : Value → Code Value) (f : (x : α) → β x) (b : Bounds α) :
    Prop :=
  (∀ v n, v.expression.bound ≤ n →
    n ≤ ((p v).build n).2.1 ∧ ((p v).build n).1.expression.bound ≤ ((p v).build n).2.1) ∧
  ∀ v n s x, v.expression.bound ≤ n → v.eval s = ⌜x⌝ₜ →
    (p v).Bounded n s (b.time x) (b.peak x) (fun w t =>
      w.eval t = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j)

namespace Implements

section

variable {α : Type*} {β γ : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  [∀ x, UniqueEncoding Tree (γ x)] {p : Value → Code Value} {f : (x : α) → β x} {b c : Bounds α}

theorem mono (hp : Implements p f b)
    (h : ∀ x, b.time x ≤ c.time x ∧ b.peak x ≤ c.peak x) : Implements p f c :=
  ⟨hp.1, fun v n s x hv hx => (hp.2 v n s x hv hx).mono
    (h x).1 (h x).2 (fun _ _ hx => hx)⟩

/-- This also covers returning an input value without executing an assignment. -/
theorem size_le (hp : Implements p f b) (x : α) :
    ⌜f x⌝ₜ.size ≤ max ⌜x⌝ₜ.size (b.peak x) := by
  have h := (hp.2 .input 1 (Function.update (fun _ => Tree.nil) 0 ⌜x⌝ₜ) x
    le_rfl (by simp)).with_size_le (bound := max ⌜x⌝ₜ.size (b.peak x))
    (by intro j; by_cases h : j = 0 <;> simp [h]
        have := Tree.size_pos ⌜x⌝ₜ
        omega) (Nat.le_max_right _ _)
  obtain ⟨_, _, _, _, ⟨ho, _⟩, hs⟩ := h.exec
  simpa only [ho] using hs

/-- A program computes the code of its result from the code of its input alone, so two
specifications of one program, possibly at different source types, agree on the results of inputs
with one code. -/
theorem encode_congr {α' : Type*} {β' : α' → Type*} [UniqueEncoding Tree α']
    [∀ y, UniqueEncoding Tree (β' y)] {g : (y : α') → β' y} {c : Bounds α'}
    (hf : Implements p f b) (hg : Implements p g c) {x : α} {y : α'} (h : ⌜x⌝ₜ = ⌜y⌝ₜ) :
    ⌜f x⌝ₜ = ⌜g y⌝ₜ := by
  let s := Function.update (fun _ => Tree.nil) 0 ⌜x⌝ₜ
  obtain ⟨t, ht, hft, -⟩ := Cmd.Bounded.exec (hf.2 .input 1 s x le_rfl (by simp [s]))
  obtain ⟨u, hu, hgu, -⟩ := Cmd.Bounded.exec (hg.2 .input 1 s y le_rfl (by simp [s, h]))
  rw [← hft, ← hgu, ht.deterministic hu]

/-- Reinterpret the result without changing the program or its resources. -/
theorem of_encode {g : (x : α) → γ x} (hp : Implements p g b)
    (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ) : Implements p f b := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  simpa only [hfg] using hp.2 v n s x hv hx

/-- Continue with a program receiving both the computed value and the original input. -/
theorem bind_input {r : Value → Value → Code Value} {g : (x : α) → γ x} {time peak : α → ℕ}
    (hp : Implements p f b)
    (hr₁ : ∀ u v n, u.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((r u v).build n).2.1 ∧ ((r u v).build n).1.expression.bound ≤ ((r u v).build n).2.1)
    (hr₂ : ∀ u v n s x, u.expression.bound ≤ n → v.expression.bound ≤ n →
      u.eval s = ⌜f x⌝ₜ → v.eval s = ⌜x⌝ₜ →
      (r u v).Bounded n s (time x) (peak x) (fun w t => w.eval t = ⌜g x⌝ₜ ∧ ∀ j < n, t j = s j)) :
    Implements (fun v => do let w ← p v; r w v) g
      ⟨fun x => b.time x + time x, fun x => max (b.peak x) (peak x)⟩ := by
  obtain ⟨hpFresh, hp⟩ := hp
  constructor
  · intro v n hv
    obtain ⟨hn, hw⟩ := hpFresh v n hv
    obtain ⟨hm, hz⟩ := hr₁ _ v _ hw (hv.trans hn)
    exact ⟨hn.trans hm, hz⟩
  · intro v n s x hv hx
    obtain ⟨hn, hw⟩ := hpFresh v n hv
    apply Code.Bounded.bind ((hp v n s x hv hx).with_result.mono le_rfl
      (Nat.le_max_left _ _) (fun _ _ h => h))
    rintro w t ⟨rfl, hwVal, ht⟩
    apply (hr₂ _ v _ t x hw (hv.trans hn) hwVal ((v.eval_eq_of_forall_lt hv ht).trans hx)).mono
      le_rfl (Nat.le_max_right _ _)
    intro a u ⟨ha, hu⟩
    exact ⟨ha, fun j hj => (hu j (hj.trans_le hn)).trans (ht j hj)⟩

end

section

variable {α β : Type*} {γ : β → Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [∀ y, UniqueEncoding Tree (γ y)] {p q : Value → Code Value} {f : α → β}
  {g : (y : β) → γ y} {b : Bounds α}

/-- The type of the second result may depend on the intermediate value. -/
theorem comp {d : Bounds β} (hp : Implements p f b) (hq : Implements q g d) :
    Implements (fun v => p v >>= q) (fun x => g (f x))
      ⟨fun x => b.time x + d.time (f x), fun x => max (b.peak x) (d.peak (f x))⟩ := by
  constructor
  · intro v n hv
    obtain ⟨hn, hw⟩ := hp.1 v n hv
    obtain ⟨hm, hz⟩ := hq.1 _ _ hw
    exact ⟨hn.trans hm, hz⟩
  · intro v n s x hv hx
    obtain ⟨hn, hb⟩ := hp.1 v n hv
    apply Code.Bounded.bind ((hp.2 v n s x hv hx).with_result.mono
      le_rfl (Nat.le_max_left _ _) (fun _ _ h => h))
    intro w t ⟨hwEq, hw, hframe⟩
    subst w
    apply (hq.2 _ _ t (f x) hb hw).mono le_rfl (Nat.le_max_right _ _) ?_
    intro z u ⟨hz, hframe'⟩
    exact ⟨hz, fun j hj => (hframe' j (hj.trans_le hn)).trans (hframe j hj)⟩

end

/-- Returning the supplied input incurs no assignment or intermediate-tree cost. -/
theorem id {α : Type*} [UniqueEncoding Tree α] :
    Implements (fun v => pure v) (id : α → α) ⟨fun _ => 0, fun _ => 0⟩ :=
  ⟨fun _ _ hv => ⟨le_rfl, hv⟩,
    fun v _ _ _ _ hx => (Code.bounded_pure_iff v _).2 ⟨hx, fun _ _ => rfl⟩⟩

/-- Restrict or reinterpret inputs without changing their codes or the implementing program. -/
theorem map_input {α γ : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] [UniqueEncoding Tree γ] {p : Value → Code Value}
    {f : (x : α) → β x} {b : Bounds α} (hp : Implements p f b) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    Implements p (fun x => f (i x)) ⟨b.time ∘ i, b.peak ∘ i⟩ := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  exact hp.2 v n s (i x) hv (hx.trans (hi x).symm)

end Implements

/-- `f` is implemented by `program`, whose exact budgets have growths satisfying `time` and `peak`,
such as `IsPoly s` or `IsO(T)`. The program is a parameter, as the derivative is in `HasDerivAt`,
so that one program at every type is a statement. Statements take this form, as `ComputableIn`
does for a model. -/
def HasProgramIn {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] (f : (x : α) → β x) (program : Value → Code Value)
    (time peak : (α → ℕ) → Prop) : Prop :=
  ∃ b : Bounds α, Implements program f b ∧ time b.time ∧ peak b.peak

namespace Internal

/-- `HasProgramIn` within `O(time)` and `O(peak)`, the form the translation composes: a `fun_prop`
property of `f`. The hidden coefficient is uniform over all inputs, including repeated calls on
small inputs. A structure, so that a unification that fails is not unfolded into `Dominated`. -/
@[fun_prop]
structure HasProgramInO {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] (f : (x : α) → β x) (program : Value → Code Value)
    (time peak : α → ℕ) : Prop where
  /-- The program within `O(time)` and `O(peak)`. -/
  toHasProgramIn : HasProgramIn f program IsO(time) IsO(peak)

namespace HasProgramInO

section

variable {α : Type*} {β γ : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  [∀ x, UniqueEncoding Tree (γ x)] {f : (x : α) → β x} {program : Value → Code Value}
  {t p : α → ℕ}

/-- Some exact budgets certify the program and are dominated by the stated growth. -/
theorem sound (hf : HasProgramInO f program t p) :
    ∃ b : Bounds α, Implements program f b ∧ Dominated b.time t ∧ Dominated b.peak p :=
  hf.toHasProgramIn

/-- Use the exact budgets of a certified program as its growth specification. -/
theorem of_implements (b : Bounds α) (h : Implements program f b) :
    HasProgramInO f program b.time b.peak :=
  ⟨b, h, .refl _, .refl _⟩

/-- Weaken the growth specification of the same program. -/
theorem mono (hf : HasProgramInO f program t p) {t' p' : α → ℕ} (ht : Dominated t t')
    (hp : Dominated p p') : HasProgramInO f program t' p' := by
  obtain ⟨b, h, hbt, hbp⟩ := hf.sound
  exact ⟨b, h, hbt.trans ht, hbp.trans hp⟩

/-- A call's output fits in either its input storage or its intermediate peak. -/
theorem size_encode (hf : HasProgramInO f program t p) :
    Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => max ⌜x⌝ₜ.size (p x)) := by
  obtain ⟨b, h, -, hbp⟩ := hf.sound
  exact ((Dominated.refl _).max hbp).mono_left h.size_le

/-- Change the source function by equality, retaining the program and growth. -/
theorem congr (hf : HasProgramInO f program t p) {g : (x : α) → β x} (h : f = g) :
    HasProgramInO g program t p :=
  h ▸ hf

/-- Retain a program when only the interpretation of its encoded result changes. -/
theorem of_encode {g : (x : α) → γ x} (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ)
    (hg : HasProgramInO g program t p) : HasProgramInO f program t p := by
  obtain ⟨b, h, ht, hp⟩ := hg.sound
  exact ⟨b, h.of_encode hfg, ht, hp⟩

end

/-- Returning the supplied input incurs no assignment or intermediate-tree cost. -/
theorem identity {α : Type*} [UniqueEncoding Tree α] :
    HasProgramInO (id : α → α) (fun v => pure v) (fun _ => 0) (fun _ => 0) :=
  of_implements ⟨fun _ => 0, fun _ => 0⟩ Implements.id

variable {α β γ : Type*} {δ : β → Type*} {ε : α → Type*} [UniqueEncoding Tree α]
  [UniqueEncoding Tree β] [UniqueEncoding Tree γ] [∀ y, UniqueEncoding Tree (δ y)]
  [∀ x, UniqueEncoding Tree (ε x)] {pf pg program : Value → Code Value} {t p : α → ℕ}
  {u q : β → ℕ}

/-- Compose programs; the second call is charged at the intermediate value, and its result type
may depend on that value. Rules state their results through this; a family of encodings applied
to a computed value is not a pattern `fun_prop` can unify, so it composes with `comp`. -/
theorem comp_dependent {f : α → β} {g : (y : β) → δ y} (hf : HasProgramInO f pf t p)
    (hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => g (f x)) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) := by
  obtain ⟨b, hb, hbt, hbp⟩ := hf.sound
  obtain ⟨c, hc, hct, hcp⟩ := hg.sound
  exact ⟨_, hb.comp hc, hbt.add (hct.comp f), hbp.max (hcp.comp f)⟩

/-- Compose programs; the second call is charged at the intermediate value. -/
theorem comp {f : α → β} {g : β → γ} (hf : HasProgramInO f pf t p) (hg : HasProgramInO g pg u q) :
    HasProgramInO (g ∘ f) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) :=
  hf.comp_dependent hg

/-- Reinterpret inputs with the same codes, retaining the program. -/
theorem map_input {f : (x : α) → ε x} (hf : HasProgramInO f program t p) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    HasProgramInO (fun x => f (i x)) program (fun x => t (i x)) (fun x => p (i x)) := by
  obtain ⟨b, h, ht, hp⟩ := hf.sound
  exact ⟨_, h.map_input i hi, ht.comp i, hp.comp i⟩

end HasProgramInO

end Internal

open Internal (HasProgramInO)

namespace HasProgramIn

variable {α : Type*} {β : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]
  {f : (x : α) → β x} {program : Value → Code Value} {T P : (α → ℕ) → Prop}

/-- The time growth of some certifying budgets. -/
noncomputable def time (h : HasProgramIn f program T P) : α → ℕ := h.choose.time

/-- The peak growth of the same budgets. -/
noncomputable def peak (h : HasProgramIn f program T P) : α → ℕ := h.choose.peak

/-- The program with the growths of the chosen budgets, for the translation. -/
theorem hasProgramInO (h : HasProgramIn f program T P) : HasProgramInO f program h.time h.peak :=
  ⟨h.choose, h.choose_spec.1, .refl _, .refl _⟩

/-- An implementation within `O(time)` and `O(peak)` in the form the translation composes, with
the same growths. -/
theorem toHasProgramInO {t p : α → ℕ} (h : HasProgramIn f program IsO(t) IsO(p)) :
    HasProgramInO f program t p :=
  ⟨h⟩

theorem time_spec (h : HasProgramIn f program T P) : T h.time := h.choose_spec.2.1

theorem peak_spec (h : HasProgramIn f program T P) : P h.peak := h.choose_spec.2.2

/-- The chosen time growth of an implementation polynomial in `s` is polynomial in `s`. -/
@[dominated] theorem isPoly_time {s : α → ℕ} (h : HasProgramIn f program (IsPoly s) P) :
    IsPoly s h.time :=
  h.time_spec

/-- The chosen peak growth of an implementation polynomial in `s` is polynomial in `s`. -/
@[dominated] theorem isPoly_peak {s : α → ℕ} (h : HasProgramIn f program T (IsPoly s)) :
    IsPoly s h.peak :=
  h.peak_spec

/-- Change the function by equality, retaining the program and its growths. -/
theorem congr (h : HasProgramIn f program T P) {g : (x : α) → β x} (hfg : f = g) :
    HasProgramIn g program T P :=
  hfg ▸ h

theorem mono {T' P' : (α → ℕ) → Prop} (h : HasProgramIn f program T P)
    (ht : ∀ t, T t → T' t) (hp : ∀ p, P p → P' p) : HasProgramIn f program T' P' :=
  let ⟨b, hb, hT, hP⟩ := h
  ⟨b, hb, ht _ hT, hp _ hP⟩

end HasProgramIn

/-- Growths polynomial in `s` and `s'` make the program polynomial in them. -/
theorem Internal.HasProgramInO.hasProgramIn {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {f : (x : α) → β x} {program : Value → Code Value}
    {t p s s' : α → ℕ} (hf : HasProgramInO f program t p) (ht : IsPoly s t) (hp : IsPoly s' p) :
    HasProgramIn f program (IsPoly s) (IsPoly s') :=
  let ⟨b, hb, hbt, hbp⟩ := hf
  ⟨b, hb, ht.of_dominated hbt, hp.of_dominated hbp⟩

end Complexity.TreeProgram.Source
