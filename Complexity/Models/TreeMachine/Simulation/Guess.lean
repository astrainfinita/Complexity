/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Bank
public import Complexity.Control.BinaryChoice.Basic
public import Complexity.Encoding.Bool
public import Complexity.Encoding.List
public import Complexity.Encoding.Nat

/-!
# Guessing a bit string into a register

`guessBits f g tmp` is a stack program with binary choices on the register bank of the tree
simulation. Register `f` holds a list of units, the fuel, and register `g` starts with the empty
list. For each unit of fuel the program chooses whether to stop; if not, it chooses a bit, prepends
it to the list in register `g` and drops the unit. Register `tmp` holds the code of the bit. Under
`MonadQuant.all` every run ends with some bit string no longer than the fuel in register `g`
(`spec_guessBits_all`); under `MonadQuant.any` every such bit string is guessed by some run
(`spec_guessBits_any`). The deterministic part of each step is the tree actions of `recordBit`,
run by `build`.

The program is written on the register bank of the stack machine because tree machines do not have
choices yet; by the principle that programs are written on tree machines it would belong there.
This is the current state, not a decision.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP BinaryChoice

variable {k : ℕ} {xs : Array Bool} {f g tmp : Fin k}

/-- Prepend the bit `x` to the list in register `g` and drop the head of the list of units in
register `f`. The code of `x` is built in register `tmp` from the head of `f`, the code of a
unit. -/
def recordBit (f g tmp : Fin k) (x : Bool) : StackMachine.Program Id (Work k) Bool Unit := do
  build (.left tmp f)
  build (if x then .pair tmp tmp tmp else .nop)
  build (.pair g tmp g)
  build (.right f f)

/-- The four tree actions of `recordBit` cost at most twice the fuel register, the guess register
and a constant. -/
theorem spec_recordBit (c : StackMachine.Cfg (Work k) Bool xs) (σ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜() :: rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (x : Bool) (q : ℕ) :
    Triple ((recordBit f g tmp x).verify (semantics xs))
      (fun s t ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 3 * ∑ i, (σ i).size + q ≤ t)
      (fun _ s t ↦ ∃ σ' : Fin k → Tree, s = bank c σ' ∧ σ' f = ⌜rest⌝ₜ ∧ σ' g = ⌜x :: bs⌝ₜ ∧
        (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧ 3 * ∑ i, (σ' i).size + q ≤ t) () := by
  let σ₁ := Function.update σ tmp ⌜false⌝ₜ
  let σ₂ := Function.update σ tmp ⌜x⌝ₜ
  let σ₃ := Function.update σ₂ g ⌜x :: bs⌝ₜ
  let σ₄ := Function.update σ₃ f ⌜rest⌝ₜ
  have e₁ : (Action.left tmp f).eval σ = σ₁ := by simp [σ₁, hf, encode_prod]
  have e₂ : (if x then Action.pair tmp tmp tmp else .nop).eval σ₁ = σ₂ := by
    cases x <;> simp [σ₁, σ₂, encode_prod]
  have e₃ : (Action.pair g tmp g).eval σ₂ = σ₃ := by simp [σ₂, σ₃, hgt, hg, encode_prod]
  have e₄ : (Action.right f f).eval σ₃ = σ₄ := by simp [σ₃, σ₄, σ₂, hfg, hft, hf, encode_prod]
  have c₁ : (Action.left tmp f).sizeCost ⟨σ⟩ = (σ f).size := Action.sizeCost_left tmp f ⟨σ⟩
  have c₂ : (if x then Action.pair tmp tmp tmp else .nop).sizeCost ⟨σ₁⟩ ≤ 3 := by
    cases x <;> simp [σ₁]
  have c₃ : (Action.pair g tmp g).sizeCost ⟨σ₂⟩ ≤ (σ g).size + 4 := by
    have := size_encode_bool_le x
    simp only [Action.sizeCost_pair, σ₂, Function.update_self, Function.update_of_ne hgt,
      Tree.size_pair]
    omega
  have c₄ : (Action.right f f).sizeCost ⟨σ₃⟩ = (σ f).size := by simp [σ₃, σ₂, hfg, hft]
  have h₁ := spec_build (bank c σ) (.left tmp f) σ
    (38 * (if x then Action.pair tmp tmp tmp else .nop).sizeCost ⟨σ₁⟩ +
      (38 * (Action.pair g tmp g).sizeCost ⟨σ₂⟩ + (38 * (Action.right f f).sizeCost ⟨σ₃⟩ + q)))
    (by simp)
  have h₂ := spec_build (bank c σ₁) (if x then .pair tmp tmp tmp else .nop) σ₁
    (38 * (Action.pair g tmp g).sizeCost ⟨σ₂⟩ + (38 * (Action.right f f).sizeCost ⟨σ₃⟩ + q))
    (by simp)
  have h₃ := spec_build (bank c σ₂) (.pair g tmp g) σ₂
    (38 * (Action.right f f).sizeCost ⟨σ₃⟩ + q) (by simp)
  have h₄ := spec_build (bank c σ₃) (.right f f) σ₃ q (by simp)
  simp only [bank_bank, e₁, e₂, e₃, e₄] at h₁ h₂ h₃ h₄
  -- Each action leaves the credits of the bank before the costs of the next ones.
  have hc (u v w : ℕ) {b : ℕ} (h : u + (v + w) ≤ b) : v + u + w ≤ b := by omega
  unfold recordBit
  refine ⟨(Complexity.Program.spec_bind_of_spec h₁ fun _ ↦
    Complexity.Program.spec_bind_of_spec ⟨h₂.entails_wp_of_pre fun s t ⟨hs, ht⟩ ↦ ⟨hs, hc _ _ _ ht⟩⟩
      fun _ ↦ Complexity.Program.spec_bind_of_spec
        ⟨h₃.entails_wp_of_pre fun s t ⟨hs, ht⟩ ↦ ⟨hs, hc _ _ _ ht⟩⟩ fun _ ↦
        ⟨h₄.entails_wp_of_pre fun s t ⟨hs, ht⟩ ↦ ⟨hs, hc _ _ _ ht⟩⟩).entails_wp_of_pre_post ?_ ?_⟩
  · rintro s t ⟨rfl, ht⟩
    exact ⟨rfl, by omega⟩
  · rintro _ s t ⟨rfl, ht⟩
    refine ⟨σ₄, rfl, by simp [σ₄], by simp [σ₄, σ₃, Ne.symm hfg], fun i hif hig hit ↦ ?_, ht⟩
    simp [σ₄, σ₃, σ₂, hif, hig, hit]

/-- Choose a bit and record it. -/
def guessBit (f g tmp : Fin k) : StackMachine.Program BinaryChoice (Work k) Bool Unit := do
  (recordBit f g tmp (← choose coin)).ofId

/-- Stop when the fuel register holds the empty list; otherwise choose whether to stop, and if
not, guess a bit. The result tells whether the guess has stopped. -/
def guessStep (f g tmp : Fin k) : StackMachine.Program BinaryChoice (Work k) Bool Bool := do
  let v ← roots.ofId
  if v f then
    if ← choose coin then
      guessBit f g tmp
      pure false
    else pure true
  else pure true

/-- Guess a bit string no longer than the list of units in register `f` into register `g`, which
starts with the empty list. -/
def guessBits (f g tmp : Fin k) : StackMachine.Program BinaryChoice (Work k) Bool Unit :=
  repeatUntil (guessStep f g tmp)

/-- Under `MonadQuant.all`, the bit is any choice. The head of the fuel is given by the root of
its register: `vcgen` enters the branch of `guessStep` taking a bit also where the precondition
gives an empty fuel, and there this rule is applied with the branch condition `h` left as a goal. -/
private theorem spec_guessBit_all (c : StackMachine.Cfg (Work k) Bool xs) (σ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (q : ℕ) (h : (σ f).root = true) :
    Triple ((guessBit f g tmp).verifyWith Multiset .all (semantics xs))
      (fun s t ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 1 + 3 * ∑ i, (σ i).size + q ≤ t)
      (fun _ s t ↦ ∃ (x : Bool) (σ' : Fin k → Tree), s = bank c σ' ∧ σ' f = ⌜rest.tail⌝ₜ ∧
        σ' g = ⌜x :: bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧
        3 * ∑ i, (σ' i).size + q ≤ t) () := by
  obtain _ | ⟨u, rest⟩ := rest
  · simp [hf] at h
  simp only [List.tail_cons]
  have hp (x : Bool) := spec_recordBit c σ hfg hft hgt rest hf bs hg x q
  clear hfg hft hgt
  unfold guessBit
  vcgen [hp]
  all_goals
    cases_type* And
    subst_vars
  case vc2 => exact ⟨_, ‹_›⟩
  all_goals first | omega | exact ⟨rfl, by omega⟩

/-- Under `MonadQuant.any`, the bit is the supplied `x`; the head of the fuel is given as for
`spec_guessBit_all`. -/
private theorem spec_guessBit_any (c : StackMachine.Cfg (Work k) Bool xs) (σ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (x : Bool) (q : ℕ)
    (h : (σ f).root = true) :
    Triple ((guessBit f g tmp).verifyWith Multiset .any (semantics xs))
      (fun s t ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 1 + 3 * ∑ i, (σ i).size + q ≤ t)
      (fun _ s t ↦ ∃ σ' : Fin k → Tree, s = bank c σ' ∧ σ' f = ⌜rest.tail⌝ₜ ∧
        σ' g = ⌜x :: bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧
        3 * ∑ i, (σ' i).size + q ≤ t) () := by
  obtain _ | ⟨u, rest⟩ := rest
  · simp [hf] at h
  simp only [List.tail_cons]
  -- The recorded bit is the result of the choice, which the rule of `choose` fixes to `x`.
  have hp (a : Bool) (ha : a = x) :
      Triple ((recordBit f g tmp a).verify (semantics xs))
        (fun s t ↦ s = bank c σ ∧
          38 * (2 * (σ f).size + (σ g).size + 7) + 3 * ∑ i, (σ i).size + q ≤ t)
        (fun _ s t ↦ ∃ σ' : Fin k → Tree, s = bank c σ' ∧ σ' f = ⌜rest⌝ₜ ∧ σ' g = ⌜x :: bs⌝ₜ ∧
          (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧ 3 * ∑ i, (σ' i).size + q ≤ t) () :=
    ha ▸ spec_recordBit c σ hfg hft hgt rest hf bs hg a q
  unfold guessBit
  vcgen [hp, spec_choose_any coin x (mem_returns_coin x)]
  all_goals
    cases_type* And
    subst_vars
  all_goals first | rfl | omega | exact ⟨rfl, by omega⟩

/-- Under `MonadQuant.all`, a step stops, or guesses a bit and drops a unit of a nonempty fuel. -/
private theorem spec_guessStep_all (c : StackMachine.Cfg (Work k) Bool xs) (σ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (q : ℕ) :
    Triple ((guessStep f g tmp).verifyWith Multiset .all (semantics xs))
      (fun s b ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 3 + 3 * ∑ i, (σ i).size + q ≤ b)
      (fun r s b ↦ if r then s = bank c σ ∧ 3 * ∑ i, (σ i).size + q ≤ b else
        rest ≠ [] ∧ ∃ (x : Bool) (σ' : Fin k → Tree), s = bank c σ' ∧ σ' f = ⌜rest.tail⌝ₜ ∧
          σ' g = ⌜x :: bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧
          3 * ∑ i, (σ' i).size + q ≤ b) () := by
  have hr := spec_roots (bank c σ) σ (by simp)
  have hp := spec_guessBit_all c σ hfg hft hgt rest hf bs hg q
  clear hfg hft hgt
  have hne (h : (σ f).root = true) : rest ≠ [] := by
    rintro rfl
    simp [hf] at h
  unfold guessStep
  vcgen [hr, hp]
  all_goals
    cases_type* And
    subst_vars
  case vc3 => exact ⟨hne ‹_›, ‹_›⟩
  case vc4 => assumption
  all_goals first | rfl | exact ⟨rfl, by omega⟩ | omega

/-- Under `MonadQuant.any`, a step on a nonempty fuel can guess the bit `x`. -/
private theorem spec_guessStep_any_next (c : StackMachine.Cfg (Work k) Bool xs)
    (σ : Fin k → Tree) (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜() :: rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (x : Bool) (q : ℕ) :
    Triple ((guessStep f g tmp).verifyWith Multiset .any (semantics xs))
      (fun s b ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 3 + 3 * ∑ i, (σ i).size + q ≤ b)
      (fun r s b ↦ r = false ∧ ∃ σ' : Fin k → Tree, s = bank c σ' ∧ σ' f = ⌜rest⌝ₜ ∧
          σ' g = ⌜x :: bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ' i = σ i) ∧
          3 * ∑ i, (σ' i).size + q ≤ b) () := by
  have hr := spec_roots (bank c σ) σ (by simp)
  have hroot : (σ f).root = true := by simp [hf]
  have hp := spec_guessBit_any c σ hfg hft hgt (() :: rest) hf bs hg x q hroot
  clear hfg hft hgt
  unfold guessStep
  vcgen [hr, hp, spec_choose_any coin true (mem_returns_coin true)]
  all_goals
    cases_type* And
    subst_vars
  all_goals first | rfl | contradiction | assumption | exact ⟨rfl, by omega⟩ | omega

/-- Under `MonadQuant.any`, a step can stop. -/
private theorem spec_guessStep_any_stop (c : StackMachine.Cfg (Work k) Bool xs)
    (σ : Fin k → Tree) (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (rest : List Unit)
    (hf : σ f = ⌜rest⌝ₜ) (bs : List Bool) (hg : σ g = ⌜bs⌝ₜ) (q : ℕ) :
    Triple ((guessStep f g tmp).verifyWith Multiset .any (semantics xs))
      (fun s b ↦ s = bank c σ ∧
        38 * (2 * (σ f).size + (σ g).size + 7) + 3 + 3 * ∑ i, (σ i).size + q ≤ b)
      (fun r s b ↦ r = true ∧ s = bank c σ ∧ 3 * ∑ i, (σ i).size + q ≤ b) () := by
  have hr := spec_roots (bank c σ) σ (by simp)
  have hp := spec_guessBit_any c σ hfg hft hgt rest hf bs hg false q
  clear hfg hft hgt
  unfold guessStep
  vcgen [hr, hp, spec_choose_any coin false (mem_returns_coin false)]
  all_goals
    cases_type* And
    subst_vars
  all_goals first | rfl | contradiction | omega | exact ⟨rfl, by omega⟩

/-- A step with `fuel.length - j` units of fuel left and `j` bits guessed costs at most
`152 * fuel.length + 384`, with the dispatch of the loop. -/
private theorem guessStep_cost_le {fuel : List Unit} {bs : List Bool} {j : ℕ}
    (hj : j ≤ fuel.length) (hbs : bs.length = j) :
    38 * (2 * ⌜fuel.drop j⌝ₜ.size + ⌜bs⌝ₜ.size + 7) + 4 ≤ 152 * fuel.length + 384 := by
  have := size_encode_list_bool_le bs
  rw [size_encode_list_unit, List.length_drop]
  omega

/-- `m + 1` steps of cost `152 * n + 384` fit in the time of `guessBits` when `m ≤ n`. -/
private theorem guessBits_time_le {n m : ℕ} (h : m ≤ n) :
    (152 * n + 384) * m + (152 * n + 384) ≤ 400 * (n + 1) ^ 2 := by
  rw [← Nat.mul_add_one, Nat.pow_two, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Every run ends with some bit string no longer than the fuel in register `g`; the registers
other than `f`, `g` and `tmp` keep their trees. The time is quadratic in the fuel, since each step
reads the fuel and the guess. -/
theorem spec_guessBits_all (c : StackMachine.Cfg (Work k) Bool xs) (ρ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (fuel : List Unit) (hf : ρ f = ⌜fuel⌝ₜ)
    (hg : ρ g = .nil) (q : ℕ) :
    Triple ((guessBits f g tmp).verifyWith Multiset .all (semantics xs))
      (fun s b ↦ s = bank c ρ ∧ 400 * (fuel.length + 1) ^ 2 + 3 * ∑ i, (ρ i).size + q ≤ b)
      (fun _ s b ↦ ∃ (bs : List Bool) (ρ' : Fin k → Tree), bs.length ≤ fuel.length ∧
        s = bank c ρ' ∧ ρ' g = ⌜bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → ρ' i = ρ i) ∧
        3 * ∑ i, (ρ' i).size + q ≤ b) () := by
  obtain ⟨n, hn⟩ : ∃ n, fuel.length = n := ⟨_, rfl⟩
  -- `D` bounds the cost of one step.
  obtain ⟨D, hD⟩ : ∃ D, 152 * n + 384 = D := ⟨_, rfl⟩
  rw [hn]
  let I : StackMachine.Cfg (Work k) Bool xs → ℕ → Prop := fun s b ↦
    ∃ (bs : List Bool) (σ : Fin k → Tree), bs.length ≤ n ∧ s = bank c σ ∧
      σ f = ⌜fuel.drop bs.length⌝ₜ ∧ σ g = ⌜bs⌝ₜ ∧
      (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ i = ρ i) ∧
      D * (n - bs.length) + D + 3 * ∑ i, (σ i).size + q ≤ b
  have h := Program.spec_repeatUntilWith_nop idle (guessStep f g tmp) (semantics xs) I
    (fun _ s b ↦ ∃ (bs : List Bool) (ρ' : Fin k → Tree), bs.length ≤ n ∧
      s = bank c ρ' ∧ ρ' g = ⌜bs⌝ₜ ∧ (∀ i, i ≠ f → i ≠ g → i ≠ tmp → ρ' i = ρ i) ∧
      3 * ∑ i, (ρ' i).size + q ≤ b) () (by simp)
    (fun s b ⟨_, _, _, _, _, _, _, hb⟩ ↦ by omega) ⟨fun s b ⟨bs, σ, hbn, hs, hσf, hσg, hσ, hb⟩ ↦ by
      have hcost := guessStep_cost_le (hn ▸ hbn) (rfl : bs.length = bs.length)
      rw [hn, hD, ← hσf, ← hσg] at hcost
      refine (Triple.entails_wp_of_post (spec_guessStep_all c σ hfg hft hgt _ hσf bs hσg
        (D * (n - bs.length) + q)) ?_) s b ⟨hs, by omega⟩
      rintro (_ | _) s' b' h
      · obtain ⟨hne, x, σ', rfl, h₁, h₂, h₃, h₄⟩ := h
        have hlt : bs.length < n := by
          rw [ne_eq, List.drop_eq_nil_iff, hn] at hne
          omega
        have hd : D * (n - bs.length) = D * (n - (x :: bs).length) + D := by
          rw [List.length_cons, ← Nat.mul_add_one, ← Nat.sub_add_comm hlt, Nat.add_sub_add_right]
        refine ⟨x :: bs, σ', hlt, rfl, ?_, h₂, fun i h₁ h₂ h₃' ↦ (h₃ i h₁ h₂ h₃').trans
          (hσ i h₁ h₂ h₃'), by omega⟩
        rw [h₁, List.tail_drop, List.length_cons]
      · obtain ⟨rfl, hb'⟩ := h
        exact ⟨bs, σ, hbn, rfl, hσg, hσ, by omega⟩⟩
  constructor
  rintro s b ⟨rfl, hb⟩
  refine h.le_wp _ b ⟨[], ρ, Nat.zero_le _, rfl, hf, hg, fun _ _ _ _ ↦ rfl, ?_⟩
  have := guessBits_time_le (le_refl n)
  rw [hD] at this
  simp only [List.length_nil, Nat.sub_zero]
  omega

/-- For each bit string no longer than the fuel, some run ends with it in register `g`; the
registers other than `f`, `g` and `tmp` keep their trees. The chosen bits are the bits of `bs` from
the last, since each is prepended. -/
theorem spec_guessBits_any (c : StackMachine.Cfg (Work k) Bool xs) (ρ : Fin k → Tree)
    (hfg : f ≠ g) (hft : f ≠ tmp) (hgt : g ≠ tmp) (fuel : List Unit) (hf : ρ f = ⌜fuel⌝ₜ)
    (hg : ρ g = .nil) (bs : List Bool) (hbs : bs.length ≤ fuel.length) (q : ℕ) :
    Triple ((guessBits f g tmp).verifyWith Multiset .any (semantics xs))
      (fun s b ↦ s = bank c ρ ∧ 400 * (fuel.length + 1) ^ 2 + 3 * ∑ i, (ρ i).size + q ≤ b)
      (fun _ s b ↦ ∃ ρ' : Fin k → Tree, s = bank c ρ' ∧ ρ' g = ⌜bs⌝ₜ ∧
        (∀ i, i ≠ f → i ≠ g → i ≠ tmp → ρ' i = ρ i) ∧ 3 * ∑ i, (ρ' i).size + q ≤ b) () := by
  obtain ⟨n, hn⟩ : ∃ n, fuel.length = n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, bs.length = m := ⟨_, rfl⟩
  -- `D` bounds the cost of one step.
  obtain ⟨D, hD⟩ : ∃ D, 152 * n + 384 = D := ⟨_, rfl⟩
  rw [hn] at hbs ⊢
  rw [hm] at hbs
  -- After `j` steps, register `g` holds the last `j` bits of `bs`.
  let I (j : ℕ) (s : StackMachine.Cfg (Work k) Bool xs) (b : ℕ) : Prop :=
    ∃ σ : Fin k → Tree, s = bank c σ ∧ σ f = ⌜fuel.drop j⌝ₜ ∧ σ g = ⌜bs.drop (m - j)⌝ₜ ∧
      (∀ i, i ≠ f → i ≠ g → i ≠ tmp → σ i = ρ i) ∧ D * (m - j) + D + 3 * ∑ i, (σ i).size + q ≤ b
  -- The cost of a step after `j` steps.
  have hcost {j : ℕ} (hj : j ≤ m) {σ : Fin k → Tree} (hσf : σ f = ⌜fuel.drop j⌝ₜ)
      (hσg : σ g = ⌜bs.drop (m - j)⌝ₜ) :
      38 * (2 * (σ f).size + (σ g).size + 7) + 4 ≤ D := by
    have h := guessStep_cost_le (hn ▸ hj.trans hbs)
      (by rw [List.length_drop, hm]; omega : (bs.drop (m - j)).length = j)
    rwa [hn, hD, ← hσf, ← hσg] at h
  have h := Program.spec_repeatUntilWith_count_of_invariant idle (guessStep f g tmp) (semantics xs)
    I (fun s b ↦ ∃ ρ' : Fin k → Tree, s = bank c ρ' ∧ ρ' g = ⌜bs⌝ₜ ∧
      (∀ i, i ≠ f → i ≠ g → i ≠ tmp → ρ' i = ρ i) ∧ 3 * ∑ i, (ρ' i).size + q ≤ b) m
    (fun _ _ s b h ↦ by simpa using h) (fun _ _ s b ⟨_, _, _, _, _, hb⟩ ↦ by omega)
    (fun j hjm ↦ ⟨fun s b ⟨σ, hs, hσf, hσg, hσ, hb⟩ ↦ by
      -- Guess the bit `bs[m - (j + 1)]`.
      have hc := hcost hjm.le hσf hσg
      have hd : D * (m - j) = D * (m - (j + 1)) + D := by
        rw [← Nat.mul_add_one, ← Nat.sub_add_comm hjm, Nat.add_sub_add_right]
      have hfj : fuel.drop j = () :: fuel.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
      have hi : m - (j + 1) < bs.length := by omega
      have hbj : bs.drop (m - (j + 1)) = bs[m - (j + 1)] :: bs.drop (m - j) := by
        rw [List.drop_eq_getElem_cons hi, ← Nat.sub_add_comm hjm, Nat.add_sub_add_right]
      refine (Triple.entails_wp_of_post (spec_guessStep_any_next c σ hfg hft hgt _
        (hσf.trans (congrArg _ hfj)) _ hσg bs[m - (j + 1)] (D * (m - (j + 1)) + D + q)) ?_)
        s b ⟨hs, by omega⟩
      rintro r s' b' ⟨rfl, σ', rfl, h₁, h₂, h₃, h₄⟩
      exact ⟨rfl, σ', rfl, h₁, hbj ▸ h₂, fun i h₁ h₂ h₃' ↦ (h₃ i h₁ h₂ h₃').trans
        (hσ i h₁ h₂ h₃'), by omega⟩⟩)
    ⟨fun s b ⟨σ, hs, hσf, hσg, hσ, hb⟩ ↦ by
      -- Stop.
      have hc := hcost le_rfl hσf hσg
      refine (Triple.entails_wp_of_post (spec_guessStep_any_stop c σ hfg hft hgt _ hσf _ hσg q)
        ?_) s b ⟨hs, by simp only [Nat.sub_self, Nat.mul_zero] at hb; omega⟩
      rintro r s' b' ⟨rfl, rfl, hb'⟩
      exact ⟨rfl, σ, rfl, by simpa using hσg, hσ, hb'⟩⟩
  constructor
  rintro s b ⟨rfl, hb⟩
  refine h.le_wp _ b ⟨ρ, rfl, hf, by simp [hg, ← hm], fun _ _ _ _ ↦ rfl, ?_⟩
  have := guessBits_time_le hbs
  rw [hD] at this
  simp only [Nat.sub_zero]
  omega

end Complexity.TreeMachine.Simulation.Program
