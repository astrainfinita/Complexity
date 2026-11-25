/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Correctness
public import Complexity.Models.TreeMachine.Simulation.Guess

/-!
# Guessing a bit string between two simulated tree machines

`bitsVerifier M₁ M₂` is a stack program with binary choices on the register bank of the tree
simulation. On the input tree `x` it keeps a copy of `x` and runs `M₁` on `x`, which computes a
list of units, the fuel; it guesses a bit string `bs` no longer than the fuel (`guessBits`), and
runs `M₂` on the pair of `x` and `bs`, emitting its result. The machines run on separate registers
(`TreeMachine.rename`): `M₁` on the first `k₁`, `M₂` on the next `k₂`, followed by the registers of
the input, of the guess and of the code of a bit. The fuel is consumed in the register of the
result of `M₁`. The deterministic parts, `front` and `back`, are tree actions and simulations of
tree machines; only the guess has choices. Under `MonadQuant.all` every run emits the result of
`M₂` on some bit string no longer than the fuel (`spec_bitsVerifier_all`); under `MonadQuant.any`
each such bit string has a run emitting the result of `M₂` on it (`spec_bitsVerifier_any`).

As for `guessBits`, the program is written on the register bank of the stack machine because tree
machines do not have choices yet; this is the current state, not a decision.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP

namespace BitsVerifier

variable (k₁ k₂ : ℕ)

/-- The registers of the first machine: the first `k₁` registers. -/
def firstRegs : Fin k₁ → Fin (k₁ + k₂ + 3) := Fin.castLE (by omega)

/-- The registers of the second machine: the next `k₂` registers. -/
def secondRegs (i : Fin k₂) : Fin (k₁ + k₂ + 3) := ⟨k₁ + i, by omega⟩

/-- The register keeping the input. -/
def inputReg : Fin (k₁ + k₂ + 3) := ⟨k₁ + k₂, by omega⟩

/-- The register of the guess. -/
def guessReg : Fin (k₁ + k₂ + 3) := ⟨k₁ + k₂ + 1, by omega⟩

/-- The register of the code of a bit. -/
def bitReg : Fin (k₁ + k₂ + 3) := ⟨k₁ + k₂ + 2, by omega⟩

variable {k₁ k₂}

/-- The index of a register of the first machine. -/
@[simp] theorem val_firstRegs (i : Fin k₁) : (firstRegs k₁ k₂ i : ℕ) = i := rfl

/-- The index of a register of the second machine. -/
@[simp] theorem val_secondRegs (i : Fin k₂) : (secondRegs k₁ k₂ i : ℕ) = k₁ + i := rfl

/-- The index of the input register. -/
@[simp] theorem val_inputReg : (inputReg k₁ k₂ : ℕ) = k₁ + k₂ := rfl

/-- The index of the guess register. -/
@[simp] theorem val_guessReg : (guessReg k₁ k₂ : ℕ) = k₁ + k₂ + 1 := rfl

/-- The index of the bit register. -/
@[simp] theorem val_bitReg : (bitReg k₁ k₂ : ℕ) = k₁ + k₂ + 2 := rfl

/-- The registers of the first machine are distinct. -/
theorem firstRegs_injective : (firstRegs k₁ k₂).Injective := Fin.castLE_injective _

/-- The registers of the second machine are distinct. -/
theorem secondRegs_injective : (secondRegs k₁ k₂).Injective := fun i j h ↦
  Fin.ext (by simpa using congrArg Fin.val h)

/-- The input register is not a register of the first machine. -/
theorem inputReg_ne_firstRegs (i : Fin k₁) : inputReg k₁ k₂ ≠ firstRegs k₁ k₂ i :=
  Fin.ne_of_val_ne (by simp only [val_inputReg, val_firstRegs]; omega)

/-- The guess register is not a register of the first machine. -/
theorem guessReg_ne_firstRegs (i : Fin k₁) : guessReg k₁ k₂ ≠ firstRegs k₁ k₂ i :=
  Fin.ne_of_val_ne (by simp only [val_guessReg, val_firstRegs]; omega)

/-- The bit register is not a register of the first machine. -/
theorem bitReg_ne_firstRegs (i : Fin k₁) : bitReg k₁ k₂ ≠ firstRegs k₁ k₂ i :=
  Fin.ne_of_val_ne (by simp only [val_bitReg, val_firstRegs]; omega)

/-- A register of the second machine is not a register of the first machine. -/
theorem secondRegs_ne_firstRegs (i : Fin k₂) (j : Fin k₁) :
    secondRegs k₁ k₂ i ≠ firstRegs k₁ k₂ j :=
  Fin.ne_of_val_ne (by simp only [val_secondRegs, val_firstRegs]; omega)

/-- A register of the second machine is not the input register. -/
theorem secondRegs_ne_inputReg (i : Fin k₂) : secondRegs k₁ k₂ i ≠ inputReg k₁ k₂ :=
  Fin.ne_of_val_ne (by simp only [val_secondRegs, val_inputReg]; omega)

/-- The input register is not the guess register. -/
theorem inputReg_ne_guessReg : inputReg k₁ k₂ ≠ guessReg k₁ k₂ :=
  Fin.ne_of_val_ne (by simp only [val_inputReg, val_guessReg]; omega)

/-- The guess register is not the bit register. -/
theorem guessReg_ne_bitReg : guessReg k₁ k₂ ≠ bitReg k₁ k₂ :=
  Fin.ne_of_val_ne (by simp only [val_guessReg, val_bitReg]; omega)

end BitsVerifier

open BitsVerifier

variable {k₁ k₂ : ℕ} [NeZero k₁] [NeZero k₂] {Q₁ Q₂ : Type} [FinEnum Q₁] [FinEnum Q₂]

/-- Load the input, copy it to the input register by pairing it with the empty guess register and
taking the left part, and run `M₁` on its registers. -/
def BitsVerifier.front (k₂ : ℕ) (M₁ : TreeMachine Id k₁ Q₁) :
    StackMachine.Program Id (Work (k₁ + k₂ + 3)) Bool Unit := do
  init (firstRegs k₁ k₂ 0)
  build (.pair (inputReg k₁ k₂) (firstRegs k₁ k₂ 0) (guessReg k₁ k₂))
  build (.left (inputReg k₁ k₂) (inputReg k₁ k₂))
  Program.loopOn idle (body (M₁.rename (firstRegs k₁ k₂))) M₁.q₀

/-- Pair the input with the guess in the input register of `M₂`, run `M₂` on its registers and
emit its result. -/
def BitsVerifier.back (k₁ : ℕ) (M₂ : TreeMachine Id k₂ Q₂) :
    StackMachine.Program Id (Work (k₁ + k₂ + 3)) Bool Unit := do
  build (.pair (secondRegs k₁ k₂ 0) (inputReg k₁ k₂) (guessReg k₁ k₂))
  Program.loopOn idle (body (M₂.rename (secondRegs k₁ k₂))) M₂.q₀
  IO.emitStack (data (secondRegs k₁ k₂ 0))

/-- Run `M₁` on the input, guess a bit string no longer than the fuel it computes, and run `M₂` on
the input and the guess. -/
def bitsVerifier (M₁ : TreeMachine Id k₁ Q₁) (M₂ : TreeMachine Id k₂ Q₂) :
    StackMachine.Program BinaryChoice (Work (k₁ + k₂ + 3)) Bool Unit := do
  (front k₂ M₁).ofId
  guessBits (firstRegs k₁ k₂ 0) (guessReg k₁ k₂) (bitReg k₁ k₂)
  (back k₁ M₂).ofId

namespace BitsVerifier

/-- `front` leaves the result of `M₁` in its register, the input in its register, and the
registers of the guess and of `M₂` empty. -/
theorem spec_front (k₂ : ℕ) (M₁ : TreeMachine Id k₁ Q₁) {x y : Tree} {t s : ℕ}
    (h : M₁.ComputesWithin x y t s) (q : ℕ) :
    Triple ((front k₂ M₁).verify (semantics (BitList.encodeTree x).toArray))
      (fun c b ↦ c = StackMachine.Cfg.init (Work (k₁ + k₂ + 3)) (BitList.encodeTree x) ∧
        85 * x.size + 3 * (k₁ + k₂) + 40 * t + 164 + q ≤ b)
      (fun _ c b ↦ ∃ σ : Fin (k₁ + k₂ + 3) → Tree,
        c = bank (loadedCfg (firstRegs k₁ k₂ 0) x) σ ∧ σ (firstRegs k₁ k₂ 0) = y ∧
        σ (inputReg k₁ k₂) = x ∧ σ (guessReg k₁ k₂) = .nil ∧
        (∀ i, σ (secondRegs k₁ k₂ i) = .nil) ∧ 3 * ∑ i, (σ i).size + q ≤ b) () := by
  let c₀ := loadedCfg (firstRegs k₁ k₂ 0) x
  let σ₀ := input (firstRegs k₁ k₂ 0) x
  let σ₁ := Function.update σ₀ (inputReg k₁ k₂) (.pair x .nil)
  let σ₂ := Function.update σ₀ (inputReg k₁ k₂) x
  have hm₀ : ∑ i, (σ₀ i).size = x.size + (k₁ + k₂ + 3 - 1) := sum_size_input _ x
  have e₁ : (Action.pair (inputReg k₁ k₂) (firstRegs k₁ k₂ 0) (guessReg k₁ k₂)).eval σ₀ = σ₁ := by
    simp [σ₁, σ₀, guessReg_ne_firstRegs]
  have e₂ : (Action.left (inputReg k₁ k₂) (inputReg k₁ k₂)).eval σ₁ = σ₂ := by simp [σ₁, σ₂]
  -- Each copying action costs the size of the input paired with the empty tree.
  have c₁ : (Action.pair (inputReg k₁ k₂) (firstRegs k₁ k₂ 0) (guessReg k₁ k₂)).sizeCost ⟨σ₀⟩ =
      x.size + 2 := by
    simp [σ₀, guessReg_ne_firstRegs]
    omega
  have c₂ : (Action.left (inputReg k₁ k₂) (inputReg k₁ k₂)).sizeCost ⟨σ₁⟩ = x.size + 2 := by
    simp [σ₁]
    omega
  have hσ₂ : σ₂ ∘ firstRegs k₁ k₂ = input 0 x := by
    rw [Function.update_comp_eq_of_forall_ne _ _ fun i ↦ (inputReg_ne_firstRegs i).symm]
    exact input_comp firstRegs_injective 0 x
  have hi := spec_init (firstRegs k₁ k₂ 0) x
    (38 * (x.size + 2) + 3 * ∑ i, (σ₀ i).size + (38 * (x.size + 2) + (40 * t + 1 + q)))
  have hb₁ := spec_build c₀ (.pair (inputReg k₁ k₂) (firstRegs k₁ k₂ 0) (guessReg k₁ k₂)) σ₀
    (38 * (x.size + 2) + (40 * t + 1 + q)) (loadedCfg_stacks _ _)
  have hb₂ := spec_build (bank c₀ σ₁) (.left (inputReg k₁ k₂) (inputReg k₁ k₂)) σ₁
    (40 * t + 1 + q) (by simp)
  rw [e₁, c₁] at hb₁
  rw [bank_bank, e₂, c₂] at hb₂
  have hr := spec_loopOn_rename M₁ firstRegs_injective h c₀ σ₂ hσ₂ q
  unfold front
  refine Complexity.Program.spec_bind_of_spec ⟨hi.entails_wp_of_pre ?_⟩ fun _ ↦
    Complexity.Program.spec_bind_of_spec hb₁ fun _ ↦
    Complexity.Program.spec_bind_of_spec ⟨hb₂.entails_wp_of_pre ?_⟩ fun _ ↦
    ⟨hr.entails_wp_of_pre_post ?_ ?_⟩
  -- The budget passes from one step to the next.
  iterate 3
    rintro c b ⟨rfl, hb⟩
    exact ⟨rfl, by omega⟩
  -- The registers outside those of `M₁` keep their trees.
  rintro _ c b ⟨σ, rfl, hy, hfr, hb⟩
  have hσ (j : Fin (k₁ + k₂ + 3)) (hj : ∀ i, j ≠ firstRegs k₁ k₂ i) : σ j = σ₂ j :=
    hfr j fun ⟨i, hi⟩ ↦ hj i hi.symm
  refine ⟨σ, rfl, hy, ?_, ?_, fun i ↦ ?_, hb⟩
  · simp only [hσ _ inputReg_ne_firstRegs, σ₂, Function.update_self]
  · simp only [hσ _ guessReg_ne_firstRegs, σ₂, Function.update_of_ne inputReg_ne_guessReg.symm, σ₀,
      input_get_of_ne x (guessReg_ne_firstRegs 0)]
  · simp only [hσ _ (secondRegs_ne_firstRegs i), σ₂,
      Function.update_of_ne (secondRegs_ne_inputReg i), σ₀,
      input_get_of_ne x (secondRegs_ne_firstRegs i 0)]

omit [NeZero k₁] in
/-- `back` emits the result of `M₂` on the pair of the input and the guess. -/
theorem spec_back {xs : Array Bool} (M₂ : TreeMachine Id k₂ Q₂)
    (c : StackMachine.Cfg (Work (k₁ + k₂ + 3)) Bool xs) (hc : c.output = #[])
    (σ : Fin (k₁ + k₂ + 3) → Tree) {x g : Tree} {v : Bool} {t s : ℕ}
    (hx : σ (inputReg k₁ k₂) = x) (hg : σ (guessReg k₁ k₂) = g)
    (hσ : ∀ i, σ (secondRegs k₁ k₂ i) = .nil) (h : M₂.ComputesWithin (.pair x g) ⌜v⌝ₜ t s)
    (q : ℕ) :
    Triple ((back k₁ M₂).verify (semantics xs))
      (fun c' b ↦ c' = bank c σ ∧
        38 * (x.size + g.size + 1) + 40 * t + 3 * ∑ i, (σ i).size + 12 + q ≤ b)
      (fun _ c' b ↦ c'.output = (BitList.encodeTree ⌜v⌝ₜ).toArray ∧ q ≤ b) () := by
  let σ₁ := Function.update σ (secondRegs k₁ k₂ 0) (.pair x g)
  have e : (Action.pair (secondRegs k₁ k₂ 0) (inputReg k₁ k₂) (guessReg k₁ k₂)).eval σ = σ₁ := by
    simp [σ₁, hx, hg]
  have hσ₁ : σ₁ ∘ secondRegs k₁ k₂ = input 0 (.pair x g) := by
    funext i
    by_cases hi : i = 0
    · simp [σ₁, hi]
    · simp [σ₁, hi, secondRegs_injective.eq_iff, hσ]
  have hb := spec_build (bank c σ) (.pair (secondRegs k₁ k₂ 0) (inputReg k₁ k₂) (guessReg k₁ k₂))
    σ (40 * t + 1 + (11 + q)) (by simp)
  rw [bank_bank, e] at hb
  have hr := spec_loopOn_rename M₂ secondRegs_injective h c σ₁ hσ₁ (11 + q)
  unfold back
  refine Complexity.Program.spec_bind_of_spec ⟨hb.entails_wp_of_pre_post ?_ ?_⟩ fun _ ↦
    Complexity.Program.spec_bind_of_spec hr fun _ ↦ ?_
  · rintro c' b ⟨rfl, hb'⟩
    refine ⟨rfl, ?_⟩
    simp only [Action.sizeCost_pair, hx, hg, Tree.size_pair] at hb' ⊢
    omega
  · rintro _ c' b ⟨rfl, hb'⟩
    exact ⟨rfl, by omega⟩
  constructor
  rintro c' b ⟨σ₂, rfl, h₁, -, hq⟩
  have hv : (BitList.encodeTree ⌜v⌝ₜ).length ≤ 3 := by
    rw [BitList.length_encodeTree]
    exact size_encode_bool_le v
  have he := Complexity.Program.spec_exact_budget_le
    (fun z ↦ IO.spec_emitStack (bank c σ₂) (data (secondRegs k₁ k₂ 0)) z) (k := 11)
    (by rw [bank_stacks, contents_data, h₁]; omega) q
  refine (Triple.entails_wp_of_post he ?_) _ b ⟨rfl, by omega⟩
  rintro _ c'' b' ⟨rfl, hb'⟩
  exact ⟨by simp [hc, h₁], hb'⟩

end BitsVerifier

/-- The time of `bitsVerifier` on an input of size `N`, with `k` registers in the two machines, at
most `n` units of fuel, and the times `t₁` and `t₂` of the two machines: `front`, the guess and
`back`. -/
def verifierTime (k N n t₁ t₂ : ℕ) : ℕ :=
  (85 * N + 3 * k + 40 * t₁ + 164) + (400 * (n + 1) ^ 2 + (38 * (N + 4 * n + 2) + 40 * t₂ + 12))

/-- `bitsVerifier` under a quantifier `Q`, given the specification of the guess under `Q` from the
bank left by `front`: the run emits the result of `M₂` on a guessed bit string, the guessed strings
satisfying `G`. `spec_bitsVerifier_all` and `spec_bitsVerifier_any` are its two instances. -/
private theorem spec_bitsVerifier_of_guess {Q : MonadQuant Multiset}
    [MonadQuant.PureLiftT BinaryChoice Multiset Q] (M₁ : TreeMachine Id k₁ Q₁)
    (M₂ : TreeMachine Id k₂ Q₂) {x : Tree} {fuel : List Unit} {t₁ s₁ : ℕ}
    (h₁ : M₁.ComputesWithin x ⌜fuel⌝ₜ t₁ s₁) {n : ℕ} (hn : fuel.length ≤ n)
    (G : List Bool → Prop) (hG : ∀ bs, G bs → bs.length ≤ fuel.length) (V : List Bool → Bool)
    {t₂ : ℕ} (h₂ : ∀ bs, G bs → ∃ s, M₂.ComputesWithin (.pair x ⌜bs⌝ₜ) ⌜V bs⌝ₜ t₂ s)
    (hguess : ∀ (σ : Fin (k₁ + k₂ + 3) → Tree) (q : ℕ), σ (firstRegs k₁ k₂ 0) = ⌜fuel⌝ₜ →
      σ (guessReg k₁ k₂) = .nil →
      Triple ((guessBits (firstRegs k₁ k₂ 0) (guessReg k₁ k₂) (bitReg k₁ k₂)).verifyWith Multiset Q
          (semantics (BitList.encodeTree x).toArray))
        (fun s b ↦ s = bank (loadedCfg (firstRegs k₁ k₂ 0) x) σ ∧
          400 * (fuel.length + 1) ^ 2 + 3 * ∑ i, (σ i).size + q ≤ b)
        (fun _ s b ↦ ∃ (bs : List Bool) (σ' : Fin (k₁ + k₂ + 3) → Tree), G bs ∧
          s = bank (loadedCfg (firstRegs k₁ k₂ 0) x) σ' ∧ σ' (guessReg k₁ k₂) = ⌜bs⌝ₜ ∧
          (∀ i, i ≠ firstRegs k₁ k₂ 0 → i ≠ guessReg k₁ k₂ → i ≠ bitReg k₁ k₂ → σ' i = σ i) ∧
          3 * ∑ i, (σ' i).size + q ≤ b) ()) :
    Triple ((bitsVerifier M₁ M₂).verifyWith Multiset Q (semantics (BitList.encodeTree x).toArray))
      (fun c b ↦ c = StackMachine.Cfg.init (Work (k₁ + k₂ + 3)) (BitList.encodeTree x) ∧
        verifierTime (k₁ + k₂) x.size n t₁ t₂ ≤ b)
      (fun _ c _ ↦ ∃ bs, G bs ∧ c.output = (BitList.encodeTree ⌜V bs⌝ₜ).toArray) () := by
  have hf := spec_front k₂ M₁ h₁
    (400 * (n + 1) ^ 2 + (38 * (x.size + 4 * n + 2) + 40 * t₂ + 12))
  unfold bitsVerifier
  refine Complexity.Program.spec_bind_of_spec
    ⟨(Complexity.Program.spec_ofId _ _ _ _).entails_wp_of_pre (hf.entails_wp_of_pre ?_)⟩
    fun _ ↦ ⟨?_⟩
  · rintro c b ⟨rfl, hb⟩
    exact ⟨rfl, hb⟩
  rintro c b ⟨σ, hc, hF, hx, hG', h2, hb⟩
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
  refine (Complexity.Program.spec_bind_of_spec
    (hguess σ (38 * (x.size + 4 * n + 2) + 40 * t₂ + 12) hF hG') fun _ ↦ ⟨?_⟩).le_wp c b
    ⟨hc, by omega⟩
  rintro c b ⟨bs, σ', hbs, hc', hg', hfr, hb'⟩
  obtain ⟨s₂, h₂⟩ := h₂ bs hbs
  -- The registers from the first of `M₂` to the input register keep their trees.
  have hk (i : Fin (k₁ + k₂ + 3)) (hi : k₁ ≤ i) (hi' : (i : ℕ) ≤ k₁ + k₂) : σ' i = σ i :=
    hfr i (Fin.ne_of_val_ne (ne_of_gt ((0 : Fin k₁).isLt.trans_le hi)))
      (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_succ_of_le hi')))
      (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_add_right 1 (Nat.lt_succ_of_le hi'))))
  have hl := size_encode_list_bool_le bs
  have hlen := hG bs hbs
  have hb := spec_back M₂ (loadedCfg (firstRegs k₁ k₂ 0) x) rfl σ'
    ((hk _ (Nat.le_add_right k₁ k₂) le_rfl).trans hx) hg'
    (fun i ↦ (hk _ (Nat.le_add_right k₁ i) (Nat.add_le_add_left i.isLt.le k₁)).trans (h2 i)) h₂ 0
  refine (Complexity.Program.spec_ofId _ _ _ _).le_wp c b
    ((hb.entails_wp_of_post ?_) c b ⟨hc', by omega⟩)
  rintro _ c' b' ⟨hc'', -⟩
  exact ⟨bs, hbs, hc''⟩

/-- Every run emits the result of `M₂` on the input and some bit string no longer than the fuel
computed by `M₁`. -/
theorem spec_bitsVerifier_all (M₁ : TreeMachine Id k₁ Q₁) (M₂ : TreeMachine Id k₂ Q₂)
    {x : Tree} {fuel : List Unit} {t₁ s₁ : ℕ} (h₁ : M₁.ComputesWithin x ⌜fuel⌝ₜ t₁ s₁)
    {n : ℕ} (hn : fuel.length ≤ n) (V : List Bool → Bool) {t₂ : ℕ}
    (h₂ : ∀ bs : List Bool, bs.length ≤ fuel.length →
      ∃ s, M₂.ComputesWithin (.pair x ⌜bs⌝ₜ) ⌜V bs⌝ₜ t₂ s) :
    Triple ((bitsVerifier M₁ M₂).verifyWith Multiset .all
        (semantics (BitList.encodeTree x).toArray))
      (fun c b ↦ c = StackMachine.Cfg.init (Work (k₁ + k₂ + 3)) (BitList.encodeTree x) ∧
        verifierTime (k₁ + k₂) x.size n t₁ t₂ ≤ b)
      (fun _ c _ ↦ ∃ bs : List Bool, bs.length ≤ fuel.length ∧
        c.output = (BitList.encodeTree ⌜V bs⌝ₜ).toArray) () :=
  spec_bitsVerifier_of_guess M₁ M₂ h₁ hn _ (fun _ h ↦ h) V h₂ fun σ q hF hG ↦
    spec_guessBits_all _ σ (guessReg_ne_firstRegs 0).symm (bitReg_ne_firstRegs 0).symm
      guessReg_ne_bitReg fuel hF hG q

/-- For each bit string `bs` no longer than the fuel computed by `M₁`, some run emits the result of
`M₂` on the input and `bs`. -/
theorem spec_bitsVerifier_any (M₁ : TreeMachine Id k₁ Q₁) (M₂ : TreeMachine Id k₂ Q₂)
    {x : Tree} {fuel : List Unit} {t₁ s₁ : ℕ} (h₁ : M₁.ComputesWithin x ⌜fuel⌝ₜ t₁ s₁)
    {n : ℕ} (hn : fuel.length ≤ n) (bs : List Bool) (hbs : bs.length ≤ fuel.length) {v : Bool}
    {t₂ s₂ : ℕ} (h₂ : M₂.ComputesWithin (.pair x ⌜bs⌝ₜ) ⌜v⌝ₜ t₂ s₂) :
    Triple ((bitsVerifier M₁ M₂).verifyWith Multiset .any
        (semantics (BitList.encodeTree x).toArray))
      (fun c b ↦ c = StackMachine.Cfg.init (Work (k₁ + k₂ + 3)) (BitList.encodeTree x) ∧
        verifierTime (k₁ + k₂) x.size n t₁ t₂ ≤ b)
      (fun _ c _ ↦ c.output = (BitList.encodeTree ⌜v⌝ₜ).toArray) () := by
  refine ⟨(spec_bitsVerifier_of_guess M₁ M₂ h₁ hn (· = bs) (fun _ h ↦ h ▸ hbs) (fun _ ↦ v)
    (fun _ h ↦ h ▸ ⟨s₂, h₂⟩) fun σ q hF hG ↦ ⟨?_⟩).entails_wp_of_post ?_⟩
  · refine (spec_guessBits_any _ σ (guessReg_ne_firstRegs 0).symm (bitReg_ne_firstRegs 0).symm
      guessReg_ne_bitReg fuel hF hG bs hbs q).entails_wp_of_post ?_
    rintro _ s b ⟨σ', h⟩
    exact ⟨bs, σ', rfl, h⟩
  · rintro _ c _ ⟨_, rfl, h⟩
    exact h

end Complexity.TreeMachine.Simulation.Program
