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

/-! # Certified implementations of source functions

`Implements` fixes one program and certifies its result, time and intermediate-tree peak with
exact budgets. `Implementation f time peak` keeps such a program together with the growth of
those budgets: one hidden coefficient covers every input, while sums, maxima and local constants
of `time` and `peak` stay visible. Each combinator states the growth it produces in its type, so a
selected implementation carries exactly one specification and calls reuse it directly.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

open TreeProgram

/-- A product of two quantities, each within a multiple of `c`, is within a multiple of `c ^ e`. -/
theorem mul_le_mul_pow_of_le_mul {a b c ka kb e : ℕ} (ha : a ≤ ka * c) (hb : b ≤ kb * c)
    (he : 2 ≤ e) (hc : 0 < c) : a * b ≤ ka * kb * c ^ e :=
  (Nat.mul_le_mul ha hb).trans (by
    rw [Nat.mul_mul_mul_comm, ← pow_two]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc he))

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

/-- One uniform program implements the function on every encoded input, preserving its context. -/
def Implements {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (p : Value → Code Value) (f : α → β) (b : Bounds α) : Prop :=
  (∀ v n, v.expression.bound ≤ n →
    n ≤ ((p v).build n).2.1 ∧ ((p v).build n).1.expression.bound ≤ ((p v).build n).2.1) ∧
  ∀ v n s x, v.expression.bound ≤ n → v.eval s = ⌜x⌝ₜ →
    (p v).Bounded n s (b.time x) (b.peak x) (fun w t =>
      w.eval t = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j)

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
    Implements (fun v => p v >>= q) (g ∘ f)
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

/-- Reinterpret the result without changing the program or its resources. -/
theorem of_encode {g : α → γ} (hp : Implements p g b)
    (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ) : Implements p f b := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  simpa only [hfg] using hp.2 v n s x hv hx

/-- Returning the supplied input incurs no assignment or intermediate-tree cost. -/
theorem id : Implements (fun v => pure v) (id : α → α) ⟨fun _ => 0, fun _ => 0⟩ :=
  ⟨fun _ _ hv => ⟨le_rfl, hv⟩,
    fun v _ _ _ _ hx => (Code.bounded_pure_iff v _).2 ⟨hx, fun _ _ => rfl⟩⟩

/-- Restrict or reinterpret inputs without changing their codes or the implementing program. -/
theorem map_input (hp : Implements p f b) (i : γ → α)
    (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    Implements p (f ∘ i) ⟨b.time ∘ i, b.peak ∘ i⟩ := by
  refine ⟨hp.1, ?_⟩
  intro v n s x hv hx
  exact hp.2 v n s (i x) hv (hx.trans (hi x).symm)

end Implements

/-- Evaluate an encoded argument and call a program, returning in a shared slot.
Branch-local allocations can start afresh at the same supply. -/
def callCode (p : Value → Code Value) (e : Expr ℕ) : Code Value :=
  ⟨fun n =>
    let c := do
      let a ← Code.eval e
      let z ← p a
      Code.write ⟨n⟩ z
    (.var n, (c.build (n + 1)).2)⟩

namespace Implements

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {p : Value → Code Value} {f : α → β} {b : Bounds α}

@[simp] theorem callCode_result (p : Value → Code Value) (e : Expr ℕ) (n : ℕ) :
    ((callCode p e).build n).1 = .var n := rfl

theorem callCode_fresh (hp : Implements p f b) (e : Expr ℕ) (n : ℕ) :
    n + 1 ≤ ((callCode p e).build n).2.1 := by
  have h := (hp.1 (.var (n + 1)) (n + 2) le_rfl).1
  exact (Nat.le_succ _).trans h

theorem callCode_bounded (hp : Implements p f b) (e : Expr ℕ)
    (n : ℕ) (s : ℕ → Tree) (x : α) {space : ℕ}
    (he : e.eval s = ⌜x⌝ₜ) (hs : e.maxSize s ≤ space) (hb : b.peak x ≤ space) :
    (callCode p e).Bounded n s (e.assignSteps + b.time x + 2) space
      (fun v t => v.eval t = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j) := by
  have hout : ⌜f x⌝ₜ.size ≤ space := hp.size_le x |>.trans
    (max_le (he ▸ e.size_eval_le_maxSize s |>.trans hs) hb)
  have hr := (hp.2 (.var (n + 1)) (n + 2)
    (Function.update s (n + 1) (e.eval s)) x le_rfl (by simp [he])).mono
      le_rfl hb (fun _ _ h => h)
  have hrun : (do
      let a ← Code.eval e
      let z ← p a
      Code.write ⟨n⟩ z).Bounded (n + 1) s (e.assignSteps + (b.time x + 2)) space
      (fun _ t => t n = ⌜f x⌝ₜ ∧ ∀ j < n, t j = s j) := by
    simp only [Code.bounded_eval_bind_iff, Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
    refine ⟨hs, Code.Bounded.bind hr ?_⟩
    intro z t ⟨hz, ht⟩
    simp only [Code.bounded_write_iff]
    refine ⟨z.assignSteps_le, hz ▸ hout, by simp [hz], ?_⟩
    intro j hj
    simpa [Nat.ne_of_lt hj, show j ≠ n + 1 by omega] using ht j (by omega)
  simpa only [Code.Bounded, callCode, Value.eval_var, Nat.add_assoc] using hrun

end Implements

/-- A fixed program for `f` whose exact budgets grow at most like `time` and `peak`.
The hidden coefficient is uniform over all inputs, including repeated calls on small inputs. -/
structure Implementation {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : α → β) (time peak : α → ℕ) where
  /-- One code generator shared by all encoded inputs. -/
  program : Value → Code Value
  /-- Some exact budgets certify the program and are dominated by the stated growth. -/
  sound : ∃ b : Bounds α, Implements program f b ∧ Dominated b.time time ∧ Dominated b.peak peak

namespace Implementation

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  [UniqueEncoding Tree γ] {f : α → β} {g : β → γ} {t p : α → ℕ} {u q : β → ℕ}

/-- Use the exact budgets of a certified program as its growth specification. -/
def ofImplements (program : Value → Code Value) (b : Bounds α) (h : Implements program f b) :
    Implementation f b.time b.peak :=
  ⟨program, b, h, .refl _, .refl _⟩

/-- Weaken the growth specification of the same program. -/
def mono (hf : Implementation f t p) {t' p' : α → ℕ} (ht : Dominated t t')
    (hp : Dominated p p') : Implementation f t' p' where
  program := hf.program
  sound := by
    obtain ⟨b, h, hbt, hbp⟩ := hf.sound
    exact ⟨b, h, hbt.trans ht, hbp.trans hp⟩

/-- A call's output fits in either its input storage or its intermediate peak. -/
theorem size_encode (hf : Implementation f t p) :
    Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => max ⌜x⌝ₜ.size (p x)) := by
  obtain ⟨b, h, -, hbp⟩ := hf.sound
  exact ((Dominated.refl _).max hbp).mono_left h.size_le

/-- One coefficient, and every larger one, scales the growth into certified exact budgets. -/
theorem exists_implements_mul (hf : Implementation f t p) :
    ∃ C, ∀ D, C ≤ D → Implements hf.program f ⟨fun x => D * t x, fun x => D * p x⟩ := by
  obtain ⟨b, h, hbt, hbp⟩ := hf.sound
  obtain ⟨C₁, h₁⟩ := dominated_iff.mp hbt
  obtain ⟨C₂, h₂⟩ := dominated_iff.mp hbp
  refine ⟨C₁ + C₂, fun D hD => h.mono fun x => ⟨?_, ?_⟩⟩
  · exact (by simpa only [smul_eq_mul] using h₁ x : b.time x ≤ C₁ * t x).trans
      (Nat.mul_le_mul_right _ (by omega))
  · exact (by simpa only [smul_eq_mul] using h₂ x : b.peak x ≤ C₂ * p x).trans
      (Nat.mul_le_mul_right _ (by omega))

/-- Certify a program at one coefficient chosen after the coefficients of its callees. -/
theorem sound_of_mul {program : Value → Code Value}
    (h : ∃ K, Implements program f ⟨fun x => K * t x, fun x => K * p x⟩) :
    ∃ b : Bounds α, Implements program f b ∧ Dominated b.time t ∧ Dominated b.peak p := by
  obtain ⟨K, hK⟩ := h
  exact ⟨_, hK, Dominated.of_le_mul K fun _ => le_rfl, Dominated.of_le_mul K fun _ => le_rfl⟩

/-- Certify a program whose calls are scaled by one coefficient chosen after its callees';
storage of its own inputs and arguments is not scaled. -/
theorem sound_of_mul_max {program : Value → Code Value} {s q : α → ℕ}
    (h : ∃ K, Implements program f ⟨fun x => K * t x, fun x => max (s x) (K * q x)⟩) :
    ∃ b : Bounds α, Implements program f b ∧ Dominated b.time t ∧
      Dominated b.peak (fun x => max (s x) (q x)) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨_, hK, Dominated.of_le_mul K fun _ => le_rfl, Dominated.of_le_mul (K + 1) fun x => ?_⟩
  exact max_le ((le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos K)))
    ((Nat.mul_le_mul_right _ (Nat.le_succ K)).trans
      (Nat.mul_le_mul_left _ (le_max_right _ _)))

theorem callCode_fresh (hf : Implementation f t p) (e : Expr ℕ) (n : ℕ) :
    n + 1 ≤ ((callCode hf.program e).build n).2.1 := by
  obtain ⟨b, h, -⟩ := hf.sound
  exact h.callCode_fresh e n

/-- Returning the supplied input incurs no assignment or intermediate-tree cost. -/
def identity : Implementation (id : α → α) (fun _ => 0) (fun _ => 0) :=
  ofImplements (fun v => pure v) ⟨fun _ => 0, fun _ => 0⟩ Implements.id

/-- Compose implementations; the second call is charged at the intermediate value. -/
def comp (hf : Implementation f t p) (hg : Implementation g u q) :
    Implementation (g ∘ f) (fun x => t x + u (f x)) (fun x => max (p x) (q (f x))) where
  program v := hf.program v >>= hg.program
  sound := by
    obtain ⟨b, hb, hbt, hbp⟩ := hf.sound
    obtain ⟨c, hc, hct, hcp⟩ := hg.sound
    exact ⟨_, hb.comp hc, hbt.add (hct.comp f), hbp.max (hcp.comp f)⟩

/-- Change the source function by equality, retaining the program and growth. -/
def congr (hf : Implementation f t p) {g : α → β} (h : f = g) : Implementation g t p :=
  ⟨hf.program, h ▸ hf.sound⟩

/-- Retain a program when only the interpretation of its encoded result changes. -/
def ofEncode {f : α → β} {g : α → γ} (hfg : ∀ x, ⌜f x⌝ₜ = ⌜g x⌝ₜ)
    (hg : Implementation g t p) : Implementation f t p where
  program := hg.program
  sound := by
    obtain ⟨b, h, ht, hp⟩ := hg.sound
    exact ⟨b, h.of_encode hfg, ht, hp⟩

/-- Reinterpret inputs with the same codes, retaining the program. -/
def mapInput (hf : Implementation f t p) (i : γ → α) (hi : ∀ x, ⌜i x⌝ₜ = ⌜x⌝ₜ) :
    Implementation (f ∘ i) (fun x => t (i x)) (fun x => p (i x)) where
  program := hf.program
  sound := by
    obtain ⟨b, h, ht, hp⟩ := hf.sound
    exact ⟨_, h.map_input i hi, ht.comp i, hp.comp i⟩

end Implementation

end Complexity.TreeProgram.Source
