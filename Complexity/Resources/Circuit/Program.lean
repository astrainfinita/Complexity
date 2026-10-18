/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library
public import Complexity.Resources.Circuit.Tseitin

/-! # A certified tree-machine implementation of the Tseitin transformation -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

/-- The Tseitin clauses of a gate, its input wires and its output wire. -/
def gateClauses {α : Type*}
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → α) × α) : CNF α :=
  CNF.ofGate x.2.1 x.2.2.1 x.2.2.2

theorem gateClauses_size_le {α : Type*} [UniqueEncoding Tree α]
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → α) × α) :
    ⌜gateClauses x⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size := by
  rcases x with ⟨k, op, args, out⟩
  exact CNF.size_encode_ofGate_le op args out

@[source] def gateClausesImpl {α : Type*} [UniqueEncoding Tree α] :
    Implementation (gateClauses (α := α)) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  exact (Dominated.refl _).max_same (Dominated.of_le_mul _ gateClauses_size_le)

theorem gateClauses_ftisp {α : Type*} [UniqueEncoding Tree α] :
    gateClauses (α := α) ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

/-- Add a gate's clauses to the reversed clause accumulator. -/
def accumulateGate
    (input : CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

/-- Inputs of `accumulateGate`: the clause accumulator and one gate. -/
abbrev AccumulateInput := CNF ℕ ×
  (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)

@[source] def accumulateGateImpl :
    Implementation accumulateGate (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hg := Dominated.of_le_mul _ (fun x : AccumulateInput => gateClauses_size_le x.2)
  have hl : Dominated (fun x : AccumulateInput => (gateClauses x.2).length) (fun _ => 1) :=
    Dominated.of_le_mul 3 (fun x => by
      simpa only [gateClauses, Nat.mul_one] using
        CNF.length_ofGate_le x.2.2.1 x.2.2.2.1 x.2.2.2.2)
  have hs : Dominated (fun x : AccumulateInput => ⌜x.2⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    Dominated.of_le fun x => by
      change _ ≤ 1 + ⌜x.1⌝ₜ.size + ⌜x.2⌝ₜ.size
      omega
  have ha : Dominated (fun x : AccumulateInput => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    Dominated.of_le fun x => by
      change _ ≤ 1 + ⌜x.1⌝ₜ.size + ⌜x.2⌝ₜ.size
      omega
  have ho := hg.trans hs
  refine (((?pair : Implementation (fun input : AccumulateInput => (input.1, gateClauses input.2))
    ?pairTime ?pairPeak).comp Implementation.prependFold).congr (by funext x; rfl)).mono ?time ?peak
  case pair => source_fun_prop
  all_goals
    simp only [size_encode_prod, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

theorem accumulateGate_ftisp :
    accumulateGate ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

/-- Output size is an ordinary property of the list fold, independent of its certification. -/
theorem accumulateGate_size (input : CNF ℕ ×
    (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) :
    ⌜accumulateGate input⌝ₜ.size + 1 = ⌜gateClauses input.2⌝ₜ.size + ⌜input.1⌝ₜ.size := by
  simpa [accumulateGate] using size_encode_list_append (gateClauses input.2).reverse input.1

abbrev TseitinState := (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ

/-- Finish an output state with its final clause and the accumulated clauses. -/
def circuitFinish (input : TseitinState) : CNF ℕ :=
  match input.1.2 with
  | .outputs select => ([.pos (select 0).val] :: input.2).reverse
  | .gate _ _ _ => input.2

/-- Remove the current gate while accumulating its clauses. -/
def circuitStep (input : TseitinState) :
    TseitinState :=
  match input.1 with
  | ⟨_, .outputs _⟩ => input
  | ⟨n, .gate (k := k) op args next⟩ =>
      (⟨n + 1, next⟩, accumulateGate (input.2, ⟨k, op, Fin.val ∘ args, n⟩))

abbrev OutputStateInput := Σ n, (Fin 1 → Fin n) × CNF ℕ
abbrev GateStateInput := Σ n, Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
  (Fin k → Fin n) × Circuit .booleanAlgebra (n + 1) 1 × CNF ℕ

def outputState (x : OutputStateInput) : TseitinState :=
  (⟨x.1, .outputs x.2.1⟩, x.2.2)

def gateState (x : GateStateInput) : TseitinState :=
  (⟨x.1, .gate x.2.2.1 x.2.2.2.1 x.2.2.2.2.1⟩, x.2.2.2.2.2)

theorem circuitState_cover (x : TseitinState) :
    (∃ y, outputState y = x) ∨ ∃ z, gateState z = x := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs s => exact Or.inl ⟨⟨n, s, acc⟩, rfl⟩
  | gate op args next => exact Or.inr ⟨⟨n, _, op, args, next, acc⟩, rfl⟩

/-- Gate input values keep the code of the gate's wire table. -/
theorem size_encode_gate_input (n : ℕ) {k : ℕ} (op : FirstOrder.Language.booleanAlgebra.Functions k)
    (args : Fin k → Fin n) :
    ⌜(⟨k, op, Fin.val ∘ args, n⟩ :
      Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)⌝ₜ.size =
      1 + ⌜k⌝ₜ.size + (1 + ⌜op⌝ₜ.size + (1 + ⌜args⌝ₜ.size + ⌜n⌝ₜ.size)) := by
  have h := encode_fin_values args
  simp only [Function.comp_def] at h
  simp only [Sigma.encode_mk, size_encode_prod, encode_fin_function, Function.comp_def, h]

@[source] def circuitStepImpl :
    Implementation circuitStep (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover outputState gateState circuitState_cover
  all_goals
    apply Dominated.of_le_mul 20
    intro x
    dsimp only [Function.comp_def, outputState, gateState]
  all_goals first
    | rcases x with ⟨n, select, acc⟩
      simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_outputs, size_encode_unit,
        max_le_iff]
      omega
    | rcases x with ⟨n, k, op, args, next, acc⟩
      have hsize := accumulateGate_size (acc, ⟨k, op, Fin.val ∘ args, n⟩)
      have hclauses := gateClauses_size_le (⟨k, op, Fin.val ∘ args, n⟩ :
        Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)
      have hgate := size_encode_gate_input n op args
      have hsucc := size_encode_nat_succ_le n
      have hvals : ⌜List.ofFn fun i => (args i).val⌝ₜ.size = ⌜List.ofFn args⌝ₜ.size := by
        simpa only [Function.comp_def] using congrArg Tree.size (encode_fin_values args)
      have htab : ⌜args⌝ₜ.size = ⌜List.ofFn args⌝ₜ.size := rfl
      simp only [Function.comp_def] at hsize hclauses hgate
      simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_gate, size_encode_unit,
        Tree.encode_self, max_le_iff, encode_fin_function] at hsize ⊢
      omega

theorem circuitStep_ftisp :
    circuitStep ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

/-- Whether the circuit still has a gate to process. -/
def circuitContinues (input : TseitinState) : Bool :=
  match input.1.2 with
  | .outputs _ => false
  | .gate _ _ _ => true

/-- Generate Tseitin clauses using a reversed accumulator. -/
def tseitinLoop : (Σ n, Circuit .booleanAlgebra n 1) → CNF ℕ → CNF ℕ
  | ⟨_, .outputs select⟩, acc => ([.pos (select 0).val] :: acc).reverse
  | ⟨n, .gate (k := k) op args next⟩, acc =>
    tseitinLoop ⟨n + 1, next⟩ (accumulateGate (acc, ⟨k, op, Fin.val ∘ args, n⟩))
termination_by input _ => input.2.size

theorem tseitinLoop_eq {n : ℕ} (c : Circuit .booleanAlgebra n 1) (acc : CNF ℕ) :
    tseitinLoop ⟨n, c⟩ acc = acc.reverse ++ c.tseitin := by
  cases c with
  | outputs select => simp [tseitinLoop, List.reverse_cons]
  | gate op args next =>
    rw [tseitinLoop, tseitinLoop_eq]
    simp [accumulateGate, gateClauses, List.reverse_append, List.append_assoc]
termination_by c.size

theorem tseitinLoop_nil (input : Σ n, Circuit .booleanAlgebra n 1) :
    tseitinLoop input [] = input.2.tseitin := by
  simpa using tseitinLoop_eq input.2 []

-- The recursive equation is checked on the source function, independently of generated code.
theorem tseitinLoop_step (x : TseitinState) :
    tseitinLoop x.1 x.2 = if circuitContinues x then
      tseitinLoop (circuitStep x).1 (circuitStep x).2 else circuitFinish x := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c <;> simp [circuitContinues, circuitStep, circuitFinish, tseitinLoop]

theorem tseitinLoop_state_size (x y : TseitinState)
    (hi : ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size ∧ tseitinLoop y.1 y.2 = tseitinLoop x.1 x.2) :
    ⌜y⌝ₜ.size ≤ 10 * ⌜x⌝ₜ.size ^ 2 := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  rcases y with ⟨⟨m, d⟩, bs⟩
  have hx := size_encode_list_append acc.reverse c.tseitin
  have hy := size_encode_list_append bs.reverse d.tseitin
  have he := congrArg (fun a : CNF ℕ => ⌜a⌝ₜ.size) hi.2
  simp only [tseitinLoop_eq, size_encode_reverse] at he hx hy
  have hc : ⌜(m, d)⌝ₜ.size ≤ ⌜(n, c)⌝ₜ.size := hi.1
  have hl : ⌜((m, d), bs)⌝ₜ.size ≤ ⌜((n, c), acc)⌝ₜ.size + ⌜c.tseitin⌝ₜ.size := by
    simp only [size_encode_prod] at hc ⊢
    omega
  have hp : ⌜(n, c)⌝ₜ.size ≤ ⌜((n, c), acc)⌝ₜ.size := by simp; omega
  have ho := c.size_encode_tseitin_le.trans (Nat.mul_le_mul_left 8 (pow_le_pow_left' hp 2))
  have hn := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜((n, c), acc)⌝ₜ.size
  change ⌜((m, d), bs)⌝ₜ.size ≤ 10 * ⌜((n, c), acc)⌝ₜ.size ^ 2
  omega

@[source] def circuitContinuesImpl :
    Implementation circuitContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

theorem circuitContinues_ftisp :
    circuitContinues ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

@[source] def circuitFinishImpl :
    Implementation circuitFinish (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

theorem circuitFinish_ftisp :
    circuitFinish ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

theorem circuitStep_circuit_size_lt
    (x : TseitinState) (ht : circuitContinues x = true) :
    ⌜(circuitStep x).1⌝ₜ.size < ⌜x.1⌝ₜ.size := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs select => cases ht
  | gate op args next =>
    have := size_encode_nat_succ_le n
    simp only [circuitStep, Sigma.encode_mk, size_encode_prod,
      Circuit.encode_gate, size_encode_unit]
    omega

def tseitinLoopImpl : Implementation (fun x : TseitinState => tseitinLoop x.1 x.2)
    (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  have hc : Dominated (fun x : TseitinState => ⌜x.1⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x => by
    rcases x with ⟨a, acc⟩; simp only [size_encode_prod]; omega
  have hm := hc.mul (Dominated.refl (fun x => ⌜x⌝ₜ.size))
  simp only [← pow_two] at hm
  source_fun_prop using loop
    (test := circuitContinues) (next := circuitStep) (finish := circuitFinish)
    (invariant := fun x y => ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size ∧
      tseitinLoop y.1 y.2 = tseitinLoop x.1 x.2)
    (measure := fun x => ⌜x.1⌝ₜ.size) (step := fun x => ⌜x⌝ₜ.size)
    (stop := fun x => ⌜x⌝ₜ.size ^ 2) (space := fun x => ⌜x⌝ₜ.size ^ 2)
  case equation => exact tseitinLoop_step
  case initial => intro x; exact ⟨le_rfl, rfl⟩
  case next_state =>
    intro x y hi ht
    refine ⟨(circuitStep_circuit_size_lt y ht).le.trans hi.1, ?_⟩
    simpa only [tseitinLoop_step y, ht, ↓reduceIte] using hi.2
  case decreases => intro x y _ ht; exact circuitStep_circuit_size_lt y ht
  case step_time =>
    apply Dominated.of_le
    intro z
    refine z.2.1.trans ?_
    rcases z.1.1 with ⟨a, acc⟩
    simp only [size_encode_prod]
    omega
  case check_time => exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
  case step_pos => exact fun _ => Tree.size_pos _
  case stop_pos => exact fun _ => Nat.pow_pos (Tree.size_pos _)
  case time =>
    simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact hm
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
  all_goals exact Dominated.of_le_mul _ (fun z => tseitinLoop_state_size z.1.1 z.1.2 z.2)

theorem tseitinLoop_ftisp :
    (fun x : TseitinState => tseitinLoop x.1 x.2) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) :=
  tseitinLoopImpl.mem_ftisp_pow (by decide)

attribute [source] tseitinLoopImpl

@[local source] theorem tseitin_source :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) =
      (fun input => tseitinLoop input []) := (funext tseitinLoop_nil).symm

theorem _root_.Complexity.Circuit.tseitin_ftisp :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) := by
  have hp : Dominated
      (fun x : Σ n, Circuit .booleanAlgebra n 1 => ⌜(x, ([] : CNF ℕ))⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    simp only [size_encode_prod, encode_list_nil, size_encode_unit, Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _), Dominated.refl _⟩,
      Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩
  model_fun_prop
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals with_reducible first
    | exact hp.pow 2
    | exact hp.le_pow (by decide)
    | exact Dominated.le_pow (Dominated.refl _) (by decide)
    | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))

end Complexity.TreeProgram.Source
