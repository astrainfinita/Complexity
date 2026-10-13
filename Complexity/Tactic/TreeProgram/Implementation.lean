/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Bounds
public import Complexity.Encoding.Prod
public import Mathlib.Control.ULiftable
public import Mathlib.Algebra.Group.ULift
public import Complexity.Tactic.TreeProgram.Attributes

/-! # Certified implementations of source functions

`Implements` fixes one program and certifies its result, time and intermediate-tree peak.
`Implementation` also stores a joint evaluation of source values and resource bounds.
Composition keeps the same program witness throughout; `Realizes` forgets its identity.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

open TreeProgram

/-- Input-dependent allowances for time and intermediate-tree size. -/
@[ext] structure Bounds (α : Type*) where
  /-- Time allowance for each source input. -/
  time : α → ℕ
  /-- Intermediate-tree size allowance for each source input. -/
  peak : α → ℕ

/-- One uniform program implements the function on every encoded input, preserving its context. -/
def Implements {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (p : Value → Code Value) (f : α → β) (b : Bounds α) : Prop :=
  (∀ v n, v.expression.bound ≤ n →
    n ≤ ((p v).build n).2.1 ∧ ((p v).build n).1.expression.bound ≤ ((p v).build n).2.1) ∧
  ∀ v n s x, v.expression.bound ≤ n → v.eval s = ⌜x⌝ₜ →
    (p v).Bounded n s (b.time x) (b.peak x) (fun w t =>
      w.eval t = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j)

/-- A resource specification that hides the implementing program. -/
def Realizes {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : α → β) (b : Bounds α) : Prop := ∃ p, Implements p f b

/-- Add sequential time allowances and take the maximum intermediate-tree allowance. -/
@[simps] def compBounds {α β : Type*} (f : α → β) (b : Bounds α) (c : Bounds β) : Bounds α :=
  ⟨fun x => b.time x + c.time (f x), fun x => max (b.peak x) (c.peak (f x))⟩

attribute [source_bounds↓] compBounds_time compBounds_peak

namespace Implements

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [UniqueEncoding Tree γ] {p q : Value → Code Value} {f : α → β} {g : β → γ}
  {b c : Bounds α}

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

theorem comp {d : Bounds β} (hp : Implements p f b) (hq : Implements q g d) :
    Implements (fun v => p v >>= q) (g ∘ f) (compBounds f b d) := by
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

/-- Reinterpret the result without changing the program or its resources. -/
theorem of_encode {g : α → γ} (hp : Implements p g b)
    (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ) : Implements p f b := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  simpa only [hfg] using hp.2 v n s x hv hx

/-- Restrict or reinterpret inputs without changing their codes or the implementing program. -/
theorem map_input (hp : Implements p f b) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    Implements p (f ∘ i) ⟨b.time ∘ i, b.peak ∘ i⟩ := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  exact hp.2 v n s (i x) hv (hx.trans (hi x).symm)

end Implements

namespace Realizes

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [UniqueEncoding Tree γ] {f : α → β} {g : β → γ} {b c : Bounds α}

theorem mono (hf : Realizes f b)
    (h : ∀ x, b.time x ≤ c.time x ∧ b.peak x ≤ c.peak x) : Realizes f c :=
  hf.elim fun p hp => ⟨p, hp.mono h⟩

theorem size_le (hf : Realizes f b) (x : α) :
    ⌜f x⌝ₜ.size ≤ max ⌜x⌝ₜ.size (b.peak x) := hf.elim fun _ hp => hp.size_le x

theorem comp {d : Bounds β} (hf : Realizes f b) (hg : Realizes g d) :
    Realizes (g ∘ f) (compBounds f b d) :=
  hf.elim fun _ hp => hg.elim fun _ hq => ⟨_, hp.comp hq⟩

end Realizes

/-- Sequential time and the maximum size of an intermediate tree. -/
@[ext] structure Cost where
  /-- Time allowance contributed by this evaluation. -/
  time : ℕ
  /-- Intermediate-tree size allowance contributed by this evaluation. -/
  peak : ℕ

instance : Monoid Cost where
  one := ⟨0, 0⟩
  mul a b := ⟨a.time + b.time, max a.peak b.peak⟩
  mul_assoc a b c := by
    change Cost.mk ((a.time + b.time) + c.time) (max (max a.peak b.peak) c.peak) =
      Cost.mk (a.time + (b.time + c.time)) (max a.peak (max b.peak c.peak))
    rw [Nat.add_assoc, Nat.max_assoc]
  one_mul a := by change Cost.mk (0 + a.time) (max 0 a.peak) = a; simp
  mul_one a := by change Cost.mk (a.time + 0) (max a.peak 0) = a; simp

@[simp] theorem Cost.one_time : (1 : Cost).time = 0 := rfl
@[simp] theorem Cost.one_peak : (1 : Cost).peak = 0 := rfl
@[simp] theorem Cost.mul_time (a b : Cost) : (a * b).time = a.time + b.time := rfl
@[simp] theorem Cost.mul_peak (a b : Cost) : (a * b).peak = max a.peak b.peak := rfl

universe u v

/-- A source evaluation with a resource annotation; `Implementation.sound` certifies it. -/
abbrev Costed (α : Type u) := Writer (ULift.{u} Cost) α

namespace Costed

variable {α : Type u} {β : Type v}

/-- The source value returned by a resource-annotated evaluation. -/
def value (x : Costed α) : α := x.run.run.1
/-- The resource annotation attached to an evaluation. -/
def cost (x : Costed α) : Cost := x.run.run.2.down

/-- Attach a fixed resource annotation to a source value. -/
def ofValue (x : α) (c : Cost) : Costed α := WriterT.mk (pure (x, ⟨c⟩))

@[simp] theorem value_ofValue (x : α) (c : Cost) : (ofValue x c).value = x := rfl
@[simp] theorem cost_ofValue (x : α) (c : Cost) : (ofValue x c).cost = c := rfl

/-- The Writer bind, allowing source and result types in different universes. -/
def bind (x : Costed α) (f : α → Costed β) : Costed β :=
  ULiftable.adaptDown (F := Costed.{max u v}) (G := Costed.{v})
    (ULiftable.up x : Costed (ULift.{v} α)) (fun a => f a.down)

@[simp] theorem value_bind (x : Costed α) (f : α → Costed β) :
    (bind x f).value = (f x.value).value := rfl

@[simp] theorem cost_bind (x : Costed α) (f : α → Costed β) :
    (bind x f).cost = x.cost * (f x.value).cost := rfl

@[simp] theorem bindM_eq_bind {γ : Type v} (x : Costed β) (f : β → Costed γ) :
    (x >>= f) = x.bind f := rfl

@[simp] theorem value_pure (a : α) : (pure a : Costed α).value = a := rfl
@[simp] theorem cost_pure (a : α) : (pure a : Costed α).cost = 1 := rfl

/-- Project input-dependent bounds from a joint evaluation. -/
@[simps] def bounds (evaluate : α → Costed β) : Bounds α :=
  ⟨fun x => (evaluate x).cost.time, fun x => (evaluate x).cost.peak⟩

end Costed

/-- A fixed implementation, its joint source evaluation, and the proof of their agreement. -/
structure Implementation {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : α → β) where
  /-- One code generator shared by all encoded inputs. -/
  program : Value → Code Value
  /-- Evaluate the source result and its certified resources together. -/
  evaluate : α → Costed β
  value_eq : ∀ x, (evaluate x).value = f x
  sound : Implements program (fun x => (evaluate x).value) (Costed.bounds evaluate)

namespace Implementation

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [UniqueEncoding Tree γ] {f : α → β} {g : β → γ}

/-- The resource bounds certified by this implementation. -/
def bounds (hf : Implementation f) : Bounds α := Costed.bounds hf.evaluate

theorem implements (hf : Implementation f) : Implements hf.program f hf.bounds := by
  simpa only [hf.value_eq, bounds] using hf.sound

theorem realizes (hf : Implementation f) : Realizes f hf.bounds := ⟨hf.program, hf.implements⟩

/-- Supply an existing fixed-program certificate without choosing a new implementation. -/
@[simps program evaluate] def ofImplements (p : Value → Code Value) (b : Bounds α)
    (hp : Implements p f b) : Implementation f where
  program := p
  evaluate x := Costed.ofValue (f x) ⟨b.time x, b.peak x⟩
  value_eq _ := rfl
  sound := hp

@[simp, source_bounds↓] theorem bounds_ofImplements (p : Value → Code Value) (b : Bounds α)
    (hp : Implements p f b) : (ofImplements p b hp).bounds = b := rfl

/-- Compose certified implementations, reusing the intermediate value and its cost. -/
@[simps program evaluate] def comp (hf : Implementation f) (hg : Implementation g) :
    Implementation (g ∘ f) where
  program v := hf.program v >>= hg.program
  evaluate x := Costed.bind (hf.evaluate x) hg.evaluate
  value_eq x := by simp only [Costed.value_bind, hf.value_eq, hg.value_eq, Function.comp_apply]
  sound := hf.sound.comp hg.sound

@[simp, source_bounds↓] theorem bounds_comp (hf : Implementation f) (hg : Implementation g) :
    (hf.comp hg).bounds = compBounds f hf.bounds hg.bounds := by
  ext x <;> simp [bounds, hf.value_eq]

/-- Change the source function by equality, preserving the joint evaluation. -/
@[simps program evaluate] def congr {g : α → β} (hf : Implementation f)
    (hfg : f = g) : Implementation g where
  program := hf.program
  evaluate := hf.evaluate
  value_eq x := (hf.value_eq x).trans (congrFun hfg x)
  sound := hf.sound

@[simp, source_bounds↓] theorem bounds_congr {g : α → β} (hf : Implementation f) (hfg : f = g) :
    (hf.congr hfg).bounds = hf.bounds := rfl

/-- Reinterpret inputs with the same codes, retaining the program and joint evaluation. -/
@[simps program evaluate] def mapInput (hf : Implementation f) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) : Implementation (f ∘ i) where
  program := hf.program
  evaluate x := hf.evaluate (i x)
  value_eq x := hf.value_eq (i x)
  sound := hf.sound.map_input i hi

@[simp, source_bounds↓] theorem bounds_mapInput (hf : Implementation f) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    (hf.mapInput i hi).bounds = ⟨hf.bounds.time ∘ i, hf.bounds.peak ∘ i⟩ := rfl

/-- Reinterpret an already computed result with the same code and resource allowances. -/
@[simps program evaluate] def mapOutput (hf : Implementation f) (o : β → γ)
    (ho : ∀ y, ⌜o y⌝ₜ = ⌜y⌝ₜ) : Implementation (o ∘ f) where
  program := hf.program
  evaluate x := Costed.bind (hf.evaluate x) (fun y => pure (o y))
  value_eq x := by simp only [Costed.value_bind, Costed.value_pure, hf.value_eq,
    Function.comp_apply]
  sound := by
    simpa only [Costed.value_bind, Costed.value_pure, Costed.bounds, Costed.cost_bind,
      Costed.cost_pure, mul_one] using hf.sound.of_encode
        (f := fun x => o (hf.evaluate x).value) (fun _ => ho _)

@[simp, source_bounds↓] theorem bounds_mapOutput (hf : Implementation f) (o : β → γ)
    (ho : ∀ y, ⌜o y⌝ₜ = ⌜y⌝ₜ) : (hf.mapOutput o ho).bounds = hf.bounds := by
  ext x <;> simp only [bounds, Costed.bounds_time, Costed.bounds_peak,
    mapOutput_evaluate, Costed.cost_bind, Costed.cost_pure, mul_one]

/-- Change only the budget, keeping the implementing program and its source result. -/
@[simps program evaluate] def rebudget (hf : Implementation f) (b : Bounds α)
    (h : ∀ x, hf.bounds.time x ≤ b.time x ∧ hf.bounds.peak x ≤ b.peak x) :
    Implementation f where
  program := hf.program
  evaluate x := Costed.ofValue (hf.evaluate x).value ⟨b.time x, b.peak x⟩
  value_eq := hf.value_eq
  sound := hf.sound.mono h

@[simp, source_bounds↓] theorem bounds_rebudget (hf : Implementation f) (b : Bounds α)
    (h : ∀ x, hf.bounds.time x ≤ b.time x ∧ hf.bounds.peak x ≤ b.peak x) :
    (hf.rebudget b h).bounds = b := rfl

/-- Retain a certified program when only the interpretation of its result changes. -/
@[simps! program] def ofEncode {g : α → γ} (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ)
    (hg : Implementation g) : Implementation f :=
  ofImplements hg.program hg.bounds (hg.implements.of_encode hfg)

@[simp, source_bounds↓] theorem bounds_ofEncode {g : α → γ} (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ)
    (hg : Implementation g) : (ofEncode hfg hg).bounds = hg.bounds := rfl

/-- Returning the supplied input incurs no assignment or intermediate-tree cost. -/
@[simps! program evaluate] def identity : Implementation (id : α → α) :=
  ofImplements (fun v => pure v) ⟨fun _ => 0, fun _ => 0⟩
    ⟨fun _ _ hv => ⟨le_rfl, hv⟩,
      fun v _ _ _ _ hx => (Code.bounded_pure_iff v _).2 ⟨hx, fun _ _ => rfl⟩⟩

@[simp, source_bounds↓] theorem bounds_identity :
    (identity (α := α)).bounds = ⟨fun _ => 0, fun _ => 0⟩ := rfl

/-- Evaluate an encoded argument and call a certified implementation, returning in a shared slot.
Branch-local allocations can start afresh at the same supply. -/
def call (hf : Implementation f) (e : Expr ℕ) : Code Value :=
  ⟨fun n =>
    let p := do
      let a ← Code.eval e
      let z ← hf.program a
      Code.write ⟨n⟩ z
    (.var n, (p.build (n + 1)).2)⟩

@[simp] theorem call_result (hf : Implementation f) (e : Expr ℕ) (n : ℕ) :
    ((hf.call e).build n).1 = .var n := rfl

theorem call_fresh (hf : Implementation f) (e : Expr ℕ) (n : ℕ) :
    n + 1 ≤ ((hf.call e).build n).2.1 := by
  have h := (hf.implements.1 (.var (n + 1)) (n + 2) le_rfl).1
  exact (Nat.le_succ _).trans h

theorem call_bounded (hf : Implementation f) (e : Expr ℕ)
    (n : ℕ) (s : ℕ → Tree) (x : α) {space : ℕ}
    (b : Bounds α := hf.bounds) (hbound : hf.bounds = b := by rfl)
    (he : e.eval s = ⌜x⌝ₜ) (hs : e.maxSize s ≤ space) (hb : b.peak x ≤ space) :
    (hf.call e).Bounded n s (e.assignSteps + b.time x + 2) space
      (fun v t => v.eval t = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j) := by
  subst b
  have hout : ⌜f x⌝ₜ.size ≤ space := hf.implements.size_le x |>.trans
    (max_le (he ▸ e.size_eval_le_maxSize s |>.trans hs) hb)
  have hp := (hf.implements.2 (.var (n + 1)) (n + 2)
    (Function.update s (n + 1) (e.eval s)) x le_rfl (by simp [he])).mono
      le_rfl hb (fun _ _ h => h)
  have hrun : (do
      let a ← Code.eval e
      let z ← hf.program a
      Code.write ⟨n⟩ z).Bounded (n + 1) s (e.assignSteps + (hf.bounds.time x + 2)) space
      (fun _ t => t n = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j) := by
    simp only [Code.bounded_eval_bind_iff, Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
    refine ⟨hs, Code.Bounded.bind hp ?_⟩
    intro z t ⟨hz, ht⟩
    simp only [Code.bounded_write_iff]
    refine ⟨z.assignSteps_le, hz ▸ hout, by simp [hz], ?_⟩
    intro j hj
    simpa [Nat.ne_of_lt hj, show j ≠ n + 1 by omega] using ht j (by omega)
  simpa only [Code.Bounded, call, Value.eval_var, Nat.add_assoc] using hrun

end Implementation

/-- Compatibility for existential specifications; the selected program need not be executable. -/
noncomputable def Realizes.implementation {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β} {b : Bounds α}
    (hf : Realizes f b) : Implementation f :=
  Implementation.ofImplements hf.choose b hf.choose_spec

@[simp, source_bounds↓] theorem Realizes.bounds_implementation {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β} {b : Bounds α}
    (hf : Realizes f b) : hf.implementation.bounds = b := rfl

end Complexity.TreeProgram.Source
