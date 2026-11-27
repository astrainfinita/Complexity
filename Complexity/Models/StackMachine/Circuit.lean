/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Basic
public import Complexity.Control.BinaryChoice.Path
public import Complexity.Models.Circuit.Unroll
public import Complexity.Models.Circuit.Term
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.Function
public import Complexity.Data.FinEnum
public import Complexity.Asymptotics.Basic
import Complexity.Asymptotics.Nat

/-!
# Bounded runs of binary-choice stack machines as circuits

`StackMachine.runCircuit` compiles a `t`-step run of a binary-choice Boolean stack machine on input
`xs` into a single-output Boolean circuit whose `t` inputs are the choice labels.

Internally, a configuration with input length `L` and stack capacity `T` occupies the wires
`RunCircuit.Wire κ Q L T`: a one-hot control state, a one-hot input head position, and a presence
wire and value wire (`OptionBool.toBits`) for each of the first `T` cells of every stack. The
output is read backwards as one more stack, so emitting a symbol pushes it. Cell `j` of a stack
holds the `j`-th symbol from its top.

One step has three layers: read the input symbol under the head, select the next control state and
the action signals (`RunCircuit.ActionBit κ Q`) from the control state, the local observation and
one fresh label wire, then apply them to every wire. A halted machine keeps its state and selects
the idle action, so the same circuit also pads finished runs. Starting from empty stacks, `t` steps
never exceed capacity `t`; `runCircuit` allocates `t + 1` cells per stack so the capacity is
non-zero even when `t = 0`.

The selection layer expands every Boolean function of the local view, so its size is exponential
in the machine description but independent of the input. The public size bound
`dominated_size_runCircuit` absorbs this machine-dependent factor into the coefficient of
`Dominated`, yielding an `O((t + 1) * (xs.length + t + 1))` gate bound. Internal wire and
control-signal types are numbered via their canonical `FinEnum` instances and kept module-private;
only `runCircuit` and its evaluation, satisfiability, and gate-count theorems are public.
-/

namespace Complexity.StackMachine

open FirstOrder FirstOrder.Language FirstOrder.BooleanAlgebra

variable {κ Γ Q : Type*}

/-! ### Stacks and actions -/

/-- The work stacks, followed by the output in reverse order as the stack `none`. -/
def Cfg.stack {xs : Array Γ} (c : Cfg κ Γ xs) : Option κ → List Γ
  | none => c.output.toList.reverse
  | some i => c.stacks i

@[simp] theorem Cfg.stack_init (xs : List Γ) (i : Option κ) : (Cfg.init κ xs).stack i = [] := by
  cases i <;> rfl

/-- The operation of an action on each stack of `Cfg.stack`; emitting pushes onto `none`. -/
def Action.stackOp (a : Action κ Γ) : Option κ → Op Γ
  | none => a.output.elim .nop .push
  | some i => a.work i

theorem Cfg.stack_apply {xs : Array Γ} (a : Action κ Γ) (c : Cfg κ Γ xs) (i : Option κ) :
    (apply a c).stack i = (a.stackOp i).apply (c.stack i) := by
  cases i with
  | none => cases h : a.output <;> simp [Cfg.stack, Action.stackOp, h, Op.apply]
  | some i => rfl

theorem observe_eq {xs : Array Γ} (c : Cfg κ Γ xs) :
    (observe c : Option Γ × (κ → Option Γ)) =
      (Input.read xs c.inputPos.val, fun i ↦ (c.stack (some i))[0]?) := by
  simp only [observe_def, Cfg.stack, List.head?_eq_getElem?]

/-- The transition taken along label `b`; a halted machine takes the idle action. -/
def selectAction (M : StackMachine BinaryChoice κ Γ Q) (q : Q)
    (o : Option Γ × (κ → Option Γ)) (b : Fin 2) : Q × Action κ Γ :=
  if M.halt q then (q, .idle) else M.transition q o b

theorem stepAlong_eq (M : StackMachine BinaryChoice κ Γ Q) {xs : Array Γ}
    (c : Q × Cfg κ Γ xs) (b : Fin 2) :
    M.stepAlong c b = apply (M.selectAction c.1 (observe c) b) c := by
  rw [selectAction]
  split_ifs with h
  · rw [M.stepAlong_of_halted (c := c) h]
    simp
  · rw [M.stepAlong_of_not_halted (c := c) h]
    rfl

theorem length_stack_stepAlong_le (M : StackMachine BinaryChoice κ Γ Q) {xs : Array Γ}
    (c : Q × Cfg κ Γ xs) (b : Fin 2) (i : Option κ) :
    ((M.stepAlong c b).2.stack i).length ≤ (c.2.stack i).length + 1 := by
  rw [stepAlong_eq, Controller.apply_prod, Cfg.stack_apply]
  exact Op.length_apply_le _ _

theorem length_stack_foldl_stepAlong_le (M : StackMachine BinaryChoice κ Γ Q) {xs : Array Γ}
    (bs : List (Fin 2)) (c : Q × Cfg κ Γ xs) (i : Option κ) :
    ((bs.foldl M.stepAlong c).2.stack i).length ≤ (c.2.stack i).length + bs.length := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
    have := M.length_stack_stepAlong_le c b i
    simp only [List.foldl_cons, List.length_cons]
    have := ih (M.stepAlong c b)
    omega

/-! ### Wires and control signals -/

namespace RunCircuit

/-- The wires of a configuration with input length `L` and stack capacity `T`. -/
inductive Wire (κ Q : Type*) (L T : ℕ) where
  /-- The control state is `q`. -/
  | state (q : Q)
  /-- The input head is at position `p`, counting the left blank as `0`. -/
  | input (p : Fin (L + 2))
  /-- Cell `j` of stack `i` is present (`isValue = false`), or holds `true` (`isValue = true`). -/
  | cell (i : Option κ) (j : Fin T) (isValue : Bool)

instance {L T : ℕ} [FinEnum κ] [FinEnum Q] : FinEnum (Wire κ Q L T) :=
  FinEnum.ofEquiv (Q ⊕ Fin (L + 2) ⊕ (Fin T × Option κ × Bool))
    { toFun
        | .state q => .inl q
        | .input p => .inr (.inl p)
        | .cell i j v => .inr (.inr (j, i, v))
      invFun
        | .inl q => .state q
        | .inr (.inl p) => .input p
        | .inr (.inr (j, i, v)) => .cell i j v
      left_inv w := by cases w <;> rfl
      right_inv := by rintro (q | p | ⟨j, i, v⟩) <;> rfl }

/-- Number of configuration wires under the canonical `FinEnum` instance. -/
theorem card_wire [FinEnum κ] [FinEnum Q] (L T : ℕ) :
    FinEnum.card (Wire κ Q L T) = FinEnum.card Q + (L + 2) + 2 * (FinEnum.card κ + 1) * T := by
  change FinEnum.card Q + ((L + 2) + T * ((FinEnum.card κ + 1) * 2)) = _
  rw [Nat.mul_comm _ 2, Nat.mul_comm T, ← Nat.add_assoc]

/-- The control signals of an action, read by the update layer. -/
inductive ActionBit (κ Q : Type*) where
  /-- The next control state is `q`. -/
  | state (q : Q)
  /-- The input head moves left. -/
  | left
  /-- The input head moves right. -/
  | right
  /-- Stack `i` is pushed. -/
  | push (i : Option κ)
  /-- Stack `i` is popped. -/
  | pop (i : Option κ)
  /-- The symbol pushed on stack `i`, or `false`. -/
  | symbol (i : Option κ)

instance [FinEnum κ] [FinEnum Q] : FinEnum (ActionBit κ Q) :=
  FinEnum.ofEquiv (Q ⊕ Bool ⊕ (Option κ ⊕ Option κ ⊕ Option κ))
    { toFun
        | .state q => .inl q
        | .left => .inr (.inl false)
        | .right => .inr (.inl true)
        | .push i => .inr (.inr (.inl i))
        | .pop i => .inr (.inr (.inr (.inl i)))
        | .symbol i => .inr (.inr (.inr (.inr i)))
      invFun
        | .inl q => .state q
        | .inr (.inl false) => .left
        | .inr (.inl true) => .right
        | .inr (.inr (.inl i)) => .push i
        | .inr (.inr (.inr (.inl i))) => .pop i
        | .inr (.inr (.inr (.inr i))) => .symbol i
      left_inv a := by cases a <;> rfl
      right_inv := by rintro (q | (_ | _) | i | i | i) <;> rfl }

/-- Wire values of a configuration. -/
def cfgWires [DecidableEq Q] {xs : List Bool} (T : ℕ) (c : Q × Cfg κ Bool xs.toArray) :
    Wire κ Q xs.length T → Bool
  | .state q => decide (c.1 = q)
  | .input p => decide (c.2.inputPos.val = p.val)
  | .cell i j v => OptionBool.toBits (c.2.stack i)[j.val]? v

/-! ### Layers -/

/-- Control signals of a transition: its next control state and its action. -/
def actionBits [DecidableEq Q] (a : Q × Action κ Bool) : ActionBit κ Q → Bool
  | .state q => decide (a.1 = q)
  | .left => decide (a.2.inputMove = -1)
  | .right => decide (a.2.inputMove = 1)
  | .push i => match a.2.stackOp i with
    | .push _ => true
    | _ => false
  | .pop i => match a.2.stackOp i with
    | .pop => true
    | _ => false
  | .symbol i => match a.2.stackOp i with
    | .push b => b
    | _ => false

/-- The local view of a step besides the control state: the input symbol, the stack tops, and the
label. Each symbol is read through its presence and value wires. -/
inductive LocalBit (κ : Type*) where
  /-- The presence or value bit of the input symbol. -/
  | input (isValue : Bool)
  /-- The presence or value bit of the top of work stack `i`. -/
  | top (i : κ) (isValue : Bool)
  /-- The label selecting an alternative. -/
  | choice

/-- The local bits as an input bit, a bit of a stack top, or the label. -/
def LocalBit.equivSum (κ : Type*) : LocalBit κ ≃ Bool ⊕ (κ × Bool) ⊕ Unit where
  toFun
    | .input v => .inl v
    | .top i v => .inr (.inl (i, v))
    | .choice => .inr (.inr ())
  invFun
    | .inl v => .input v
    | .inr (.inl (i, v)) => .top i v
    | .inr (.inr ()) => .choice
  left_inv y := by cases y <;> rfl
  right_inv := by rintro (v | ⟨i, v⟩ | ⟨⟩) <;> rfl

instance [FinEnum κ] : FinEnum (LocalBit κ) := FinEnum.ofEquiv _ (LocalBit.equivSum κ)

/-- Decode a local view into an observation and a label. -/
def LocalBit.decode (y : LocalBit κ → Bool) : (Option Bool × (κ → Option Bool)) × Fin 2 :=
  ((OptionBool.ofBits fun v ↦ y (.input v), fun i ↦ OptionBool.ofBits fun v ↦ y (.top i v)),
    finTwoEquiv.symm (y .choice))

/-- First layer: keep every wire and the label, and add the presence and value bits of the input
symbol under the head. -/
def readTerm (xs : List Bool) (T : ℕ) :
    Option (Wire κ Q xs.length T) ⊕ Bool → booleanAlgebra.Term (Option (Wire κ Q xs.length T))
  | .inl v => .var v
  | .inr b => oneHot (List.finRange (xs.length + 2)) (fun p ↦ some (.input p))
      fun p ↦ ofBool (OptionBool.toBits (Input.read xs.toArray p.val) b)

/-- The variable of the second layer holding a local bit. -/
def localVar (xs : List Bool) (T : ℕ) [NeZero T] :
    LocalBit κ → Option (Wire κ Q xs.length T) ⊕ Bool
  | .input b => .inr b
  | .top i b => .inl (some (.cell (some i) 0 b))
  | .choice => .inl none

/-- The selection of one control signal from the one-hot state and the expansion of the local
view. It does not depend on the input. -/
def selectBit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (a : ActionBit κ Q) : booleanAlgebra.Term (Q ⊕ LocalBit κ) :=
  oneHot (FinEnum.toList Q) .inl fun q ↦
    (shannon (FinEnum.toList (LocalBit κ)) fun y ↦
      actionBits (M.selectAction q (LocalBit.decode y).1 (LocalBit.decode y).2) a).relabel .inr

/-- The variable of the second layer holding a state or a local bit. -/
def selectVar (xs : List Bool) (T : ℕ) [NeZero T] :
    Q ⊕ LocalBit κ → Option (Wire κ Q xs.length T) ⊕ Bool :=
  Sum.elim (fun q ↦ .inl (some (.state q))) (localVar xs T)

/-- Second layer: keep every wire, and select the control signals from the one-hot state and the
expansion of the local view. -/
def selectTerm [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) [NeZero T] : Wire κ Q xs.length T ⊕ ActionBit κ Q →
      booleanAlgebra.Term (Option (Wire κ Q xs.length T) ⊕ Bool)
  | .inl v => .var (.inl (some v))
  | .inr a => (selectBit M a).relabel (selectVar xs T)

/-- An input position of the third layer, or `⊥` outside the tape. -/
def inputAt (xs : List Bool) (T k : ℕ) :
    booleanAlgebra.Term (Wire κ Q xs.length T ⊕ ActionBit κ Q) :=
  if h : k < xs.length + 2 then .var (.inl (.input ⟨k, h⟩)) else ⊥

/-- A stack cell of the third layer, or `⊥` beyond the capacity. -/
def cellAt (xs : List Bool) (T : ℕ) (i : Option κ) (k : ℕ) (v : Bool) :
    booleanAlgebra.Term (Wire κ Q xs.length T ⊕ ActionBit κ Q) :=
  if h : k < T then .var (.inl (.cell i ⟨k, h⟩ v)) else ⊥

/-- Third layer: apply the selected control signals to every wire. -/
def updateTerm (xs : List Bool) (T : ℕ) :
    Wire κ Q xs.length T → booleanAlgebra.Term (Wire κ Q xs.length T ⊕ ActionBit κ Q)
  | .state q => .var (.inr (.state q))
  | .input p => branch (.var (.inr .left)) (.var (.inr .right))
      (inputAt xs T (p.val + 1) ⊔ (if p.val = 0 then inputAt xs T 0 else ⊥))
      ((if p.val = 0 then ⊥ else inputAt xs T (p.val - 1)) ⊔
        (if p.val = xs.length + 1 then inputAt xs T p.val else ⊥))
      (inputAt xs T p.val)
  | .cell i j v => branch (.var (.inr (.push i))) (.var (.inr (.pop i)))
      (if j.val = 0 then (if v then .var (.inr (.symbol i)) else ⊤)
        else cellAt xs T i (j.val - 1) v)
      (cellAt xs T i (j.val + 1) v) (cellAt xs T i j.val v)

/-! ### Correctness of the layers -/

/-- The read layer computes the input symbol under the head. -/
theorem realize_readTerm [DecidableEq Q] (xs : List Bool) (T : ℕ) (c : Q × Cfg κ Bool xs.toArray)
    (b : Bool) (o : Option (Wire κ Q xs.length T) ⊕ Bool) :
    (readTerm xs T o).realize (Option.elim · b (cfgWires T c)) =
      Sum.elim (Option.elim · b (cfgWires T c))
        (OptionBool.toBits (Input.read xs.toArray c.2.inputPos.val)) o := by
  cases o with
  | inl v => rfl
  | inr r =>
    let p₀ : Fin (xs.length + 2) := ⟨c.2.inputPos.val, by simpa using c.2.inputPos.isLt⟩
    rw [readTerm, realize_oneHot (List.mem_finRange p₀) (by simp [cfgWires, p₀, Fin.ext_iff])]
    simp [p₀]

/-- The selection layer computes the control signals of the selected action. -/
theorem realize_selectTerm [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs : List Bool) (T : ℕ) [NeZero T] (c : Q × Cfg κ Bool xs.toArray) (b : Bool)
    (o : Wire κ Q xs.length T ⊕ ActionBit κ Q) :
    (selectTerm M xs T o).realize (Sum.elim (Option.elim · b (cfgWires T c))
        (OptionBool.toBits (Input.read xs.toArray c.2.inputPos.val))) =
      Sum.elim (cfgWires T c)
        (actionBits (M.selectAction c.1 (observe c) (finTwoEquiv.symm b))) o := by
  cases o with
  | inl v => rfl
  | inr a =>
    rw [selectTerm, Term.realize_relabel, selectBit,
      realize_oneHot (FinEnum.mem_toList c.1) fun q ↦ rfl, Term.realize_relabel,
      realize_shannon_of_mem FinEnum.mem_toList, Controller.observe_prod, observe_eq]
    simp only [LocalBit.decode, Function.comp_apply, selectVar, localVar, Sum.elim_inr,
      Sum.elim_inl, Option.elim_none, Option.elim_some, cfgWires, Fin.val_zero,
      OptionBool.ofBits_toBits]

theorem realize_inputAt [DecidableEq Q] {xs : List Bool} {T : ℕ} (c : Q × Cfg κ Bool xs.toArray)
    (f : ActionBit κ Q → Bool) (k : ℕ) :
    (inputAt xs T k).realize (Sum.elim (cfgWires T c) f) = decide (c.2.inputPos.val = k) := by
  unfold inputAt
  split_ifs with h
  · simp [cfgWires]
  · have : c.2.inputPos.val < xs.length + 2 := by simpa using c.2.inputPos.isLt
    rw [realize_bot]
    exact (decide_eq_false (by omega)).symm

theorem realize_cellAt [DecidableEq Q] {xs : List Bool} {T : ℕ} (c : Q × Cfg κ Bool xs.toArray)
    (hc : ∀ i, (c.2.stack i).length ≤ T) (f : ActionBit κ Q → Bool) (i : Option κ) (k : ℕ)
    (v : Bool) :
    (cellAt xs T i k v).realize (Sum.elim (cfgWires T c) f) =
      OptionBool.toBits (c.2.stack i)[k]? v := by
  unfold cellAt
  split_ifs with h
  · simp [cfgWires]
  · have : (c.2.stack i)[k]? = none := List.getElem?_eq_none (by have := hc i; omega)
    simp [this]

/-- The update layer applies an action, provided no stack exceeds the capacity before the step. -/
theorem realize_updateTerm [DecidableEq Q] (xs : List Bool) (T : ℕ) (c : Q × Cfg κ Bool xs.toArray)
    (hc : ∀ i, (c.2.stack i).length ≤ T) (a : Q × Action κ Bool) (w : Wire κ Q xs.length T) :
    (updateTerm xs T w).realize (Sum.elim (cfgWires T c) (actionBits a)) =
      cfgWires T (apply a c) w := by
  cases w with
  | state q => simp [updateTerm, cfgWires, actionBits]
  | input p =>
    have hlt : c.2.inputPos.val < xs.length + 2 := by simpa using c.2.inputPos.isLt
    have hs : xs.toArray.size = xs.length := List.size_toArray
    obtain ⟨_, m, _, _⟩ := a
    simp only [cfgWires, Controller.apply_prod, apply_inputPos, updateTerm]
    cases m with
    | zero =>
      rw [realize_branch_else rfl rfl, realize_inputAt]
      rfl
    | neg =>
      rw [realize_branch_left rfl rfl, Bool.eq_iff_iff, decide_eq_true_eq]
      simp only [realize_sup, apply_ite (Term.realize _), realize_inputAt, realize_bot,
        Input.movePos]
      split_ifs <;> simp only [Bool.max_eq_or, bot_eq_false, Bool.or_eq_true, decide_eq_true_eq,
        Bool.false_eq_true, or_false] <;> omega
    | pos =>
      rw [realize_branch_right rfl rfl, Bool.eq_iff_iff, decide_eq_true_eq]
      simp only [realize_sup, apply_ite (Term.realize _), realize_inputAt, realize_bot,
        Input.movePos]
      split_ifs <;> simp only [Bool.max_eq_or, bot_eq_false, Bool.or_eq_true, decide_eq_true_eq,
        Bool.false_eq_true, or_false, false_or, false_iff] <;> omega
  | cell i j v =>
    simp only [cfgWires, Controller.apply_prod, Cfg.stack_apply, updateTerm]
    cases h : a.2.stackOp i with
    | nop =>
      rw [realize_branch_else (by simp [actionBits, h]) (by simp [actionBits, h]),
        realize_cellAt c hc]
      rfl
    | push b =>
      rw [realize_branch_left (by simp [actionBits, h]) (by simp [actionBits, h])]
      rcases j with ⟨_ | j, hj⟩
      · cases v <;> simp only [↓reduceIte, Bool.false_eq_true, realize_top, top_eq_true,
          Term.realize_var, Sum.elim_inr, actionBits, h, Op.apply, List.getElem?_cons_zero,
          OptionBool.toBits_false, OptionBool.toBits_true, Option.isSome_some, Option.getD_some]
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, realize_cellAt c hc, Op.apply, List.getElem?_cons_succ]
    | pop =>
      rw [realize_branch_right (by simp [actionBits, h]) (by simp [actionBits, h]),
        realize_cellAt c hc]
      simp only [Op.apply, List.getElem?_tail]

/-- Acceptance: the machine has halted and the output is `w`. -/
def acceptTerm [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool) (T : ℕ)
    (w : List Bool) : booleanAlgebra.Term (Wire κ Q xs.length T) :=
  oneHot (FinEnum.toList Q) .state (fun q ↦ ofBool (M.halt q)) ⊓
    if w.length ≤ T then
      listInf (List.finRange T) fun j ↦ listInf [false, true] fun v ↦
        literal (.cell none j v) (OptionBool.toBits w.reverse[j.val]? v)
    else ⊥

theorem realize_acceptTerm [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) (w : List Bool) (c : Q × Cfg κ Bool xs.toArray) (hc : (c.2.stack none).length ≤ T) :
    (acceptTerm M xs T w).realize (cfgWires T c) =
      decide (M.Halted c ∧ c.2.output = w.toArray) := by
  have hout : c.2.output = w.toArray ↔ c.2.stack none = w.reverse := by
    rw [Cfg.stack, List.reverse_inj, ← Array.toList_inj, List.toList_toArray]
  rw [acceptTerm, realize_inf, realize_oneHot (FinEnum.mem_toList c.1) fun q ↦ rfl]
  simp only [realize_ofBool, Bool.min_eq_and]
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, hout]
  refine and_congr Iff.rfl ?_
  split_ifs with hw
  · simp only [realize_listInf, realize_literal, cfgWires, List.all_eq_true, List.mem_finRange,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, true_implies]
    constructor
    · intro h
      apply List.ext_getElem?
      intro k
      by_cases hk : k < T
      · exact OptionBool.toBits_injective (funext fun v ↦ by cases v <;> simp [h ⟨k, hk⟩])
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · intro h j
      simp [h]
  · rw [realize_bot, show (⊥ : Bool) = false from rfl, Bool.false_eq_true, false_iff]
    intro h
    have := congrArg List.length h
    simp only [List.length_reverse] at this
    omega

/-! ### Layer circuits -/

variable {W A : ℕ}

/-- Number the variables of the read layer: the wires, then the label. -/
def readInputs {xs : List Bool} {T : ℕ} (eW : Wire κ Q xs.length T ≃ Fin W) :
    Option (Wire κ Q xs.length T) ≃ Fin (W + 1) :=
  eW.optionCongr.trans finSuccEquivLast.symm

/-- Number the outputs of the read layer: its inputs, then the input symbol. -/
def readOutputs {xs : List Bool} {T : ℕ} (eW : Wire κ Q xs.length T ≃ Fin W) :
    Option (Wire κ Q xs.length T) ⊕ Bool ≃ Fin ((W + 1) + 2) :=
  ((readInputs eW).sumCongr finTwoEquiv.symm).trans finSumFinEquiv

/-- Number the outputs of the selection layer: the wires, then the control signals. -/
def selectOutputs {xs : List Bool} {T : ℕ} (eW : Wire κ Q xs.length T ≃ Fin W)
    (eA : ActionBit κ Q ≃ Fin A) : Wire κ Q xs.length T ⊕ ActionBit κ Q ≃ Fin (W + A) :=
  (eW.sumCongr eA).trans finSumFinEquiv

/-- The read layer under the numberings. -/
def readCircuit (xs : List Bool) (T : ℕ) (eW : Wire κ Q xs.length T ≃ Fin W) :
    Circuit .booleanAlgebra (W + 1) ((W + 1) + 2) :=
  Circuit.ofTermsEquiv (readInputs eW) (readOutputs eW) (readTerm xs T)

/-- The selection layer under the numberings. -/
def selectCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) [NeZero T] (eW : Wire κ Q xs.length T ≃ Fin W) (eA : ActionBit κ Q ≃ Fin A) :
    Circuit .booleanAlgebra ((W + 1) + 2) (W + A) :=
  Circuit.ofTermsEquiv (readOutputs eW) (selectOutputs eW eA) (selectTerm M xs T)

/-- The update layer under the numberings. -/
def updateCircuit (xs : List Bool) (T : ℕ) (eW : Wire κ Q xs.length T ≃ Fin W)
    (eA : ActionBit κ Q ≃ Fin A) : Circuit .booleanAlgebra (W + A) W :=
  Circuit.ofTermsEquiv (selectOutputs eW eA) eW (updateTerm xs T)

/-- One step: the first `W` inputs are the wires under the numbering `eW`, the last is the
label. -/
def stepCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) [NeZero T] (eW : Wire κ Q xs.length T ≃ Fin W) (eA : ActionBit κ Q ≃ Fin A) :
    Circuit .booleanAlgebra (W + 1) W :=
  (readCircuit xs T eW).comp ((selectCircuit M xs T eW eA).comp (updateCircuit xs T eW eA))

/-- The step circuit follows the labelled alternative, provided no stack exceeds the capacity
before the step. -/
theorem eval_stepCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs : List Bool) (T : ℕ) [NeZero T] (eW : Wire κ Q xs.length T ≃ Fin W)
    (eA : ActionBit κ Q ≃ Fin A) (c : Q × Cfg κ Bool xs.toArray)
    (hc : ∀ i, (c.2.stack i).length ≤ T) (b : Bool) :
    (stepCircuit M xs T eW eA).eval (Fin.snoc (cfgWires T c ∘ eW.symm) b) =
      cfgWires T (M.stepAlong c (finTwoEquiv.symm b)) ∘ eW.symm := by
  have h1 : Fin.snoc (cfgWires T c ∘ eW.symm) b ∘ readInputs eW =
      (Option.elim · b (cfgWires T c)) := by
    funext o
    cases o <;> simp [readInputs, finSuccEquivLast_symm_some]
  simp only [stepCircuit, readCircuit, selectCircuit, updateCircuit, Circuit.eval_comp,
    Circuit.eval_ofTermsEquiv, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, h1,
    realize_readTerm, realize_selectTerm M xs T c, realize_updateTerm xs T c hc, stepAlong_eq]

/-- Steps along a label sequence stay exact while the stacks have room for one push per label. -/
theorem foldl_eval_stepCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs : List Bool) (T : ℕ) [NeZero T] (eW : Wire κ Q xs.length T ≃ Fin W)
    (eA : ActionBit κ Q ≃ Fin A) (l : List Bool) (c : Q × Cfg κ Bool xs.toArray)
    (hc : ∀ i, (c.2.stack i).length + l.length ≤ T) :
    l.foldl (fun s b ↦ (stepCircuit M xs T eW eA).eval (Fin.snoc s b)) (cfgWires T c ∘ eW.symm) =
      cfgWires T (l.foldl (fun c b ↦ M.stepAlong c (finTwoEquiv.symm b)) c) ∘ eW.symm := by
  induction l generalizing c with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons] at hc ⊢
    rw [eval_stepCircuit M xs T eW eA c (fun i ↦ by have := hc i; omega)]
    refine ih _ fun i ↦ ?_
    have := hc i
    have := M.length_stack_stepAlong_le c (finTwoEquiv.symm b) i
    omega

/-- The initial wire values as constants, followed by the labels. -/
def initTerm [DecidableEq Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool) (T t : ℕ) :
    Wire κ Q xs.length T ⊕ Fin t → booleanAlgebra.Term (Fin t)
  | .inl v => ofBool (cfgWires T (M.init xs) v)
  | .inr i => .var i

/-- The initial wires as constant gates, followed by the label inputs. -/
def initCircuit [DecidableEq Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T t : ℕ) (eW : Wire κ Q xs.length T ≃ Fin W) : Circuit .booleanAlgebra t (W + t) :=
  Circuit.ofTermsEquiv (Equiv.refl _) ((eW.sumCongr (Equiv.refl _)).trans finSumFinEquiv)
    (initTerm M xs T t)

theorem eval_initCircuit [DecidableEq Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T t : ℕ) (eW : Wire κ Q xs.length T ≃ Fin W) (x : Fin t → Bool) :
    (initCircuit M xs T t eW).eval x = Fin.append (cfgWires T (M.init xs) ∘ eW.symm) x := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j <;> simp [initCircuit, initTerm]

/-- Accept when the machine has halted with output `w`. -/
def acceptCircuit [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) (w : List Bool) (eW : Wire κ Q xs.length T ≃ Fin W) : Circuit .booleanAlgebra W 1 :=
  Circuit.ofTermsEquiv eW (Equiv.refl _) fun _ ↦ acceptTerm M xs T w

/-! ### Layer gate counts -/

section Size

open Circuit

theorem numFuncs_inputAt_le (xs : List Bool) (T k : ℕ) :
    (inputAt (κ := κ) (Q := Q) xs T k).numFuncs ≤ 1 := by
  unfold inputAt
  split_ifs <;> simp

theorem numFuncs_cellAt_le (xs : List Bool) (T : ℕ) (i : Option κ) (k : ℕ) (v : Bool) :
    (cellAt (Q := Q) xs T i k v).numFuncs ≤ 1 := by
  unfold cellAt
  split_ifs <;> simp

theorem numFuncs_updateTerm_le (xs : List Bool) (T : ℕ) (w : Wire κ Q xs.length T) :
    (updateTerm xs T w).numFuncs ≤ 14 := by
  cases w with
  | state q => simp [updateTerm]
  | input p =>
    simp only [updateTerm, numFuncs_branch, numFuncs_sup, Term.numFuncs_var]
    have h := numFuncs_inputAt_le (κ := κ) (Q := Q) xs T
    have := h (p.val + 1)
    have := h p.val
    have := h 0
    have := h (p.val - 1)
    split_ifs <;> simp only [numFuncs_bot] <;> omega
  | cell i j v =>
    simp only [updateTerm, numFuncs_branch, Term.numFuncs_var]
    have h := numFuncs_cellAt_le (Q := Q) xs T i
    have := h (j.val - 1) v
    have := h (j.val + 1) v
    have := h j.val v
    split_ifs <;> (try simp only [numFuncs_top, Term.numFuncs_var]) <;> omega

/-- Total gate count of the selection layer; independent of input length and stack capacity. -/
def selectSize [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) : ℕ :=
  ∑ a : ActionBit κ Q, (selectBit M a).numFuncs

/-- Every step has the same gate count: the input read is linear in the input length, the selection
depends only on the machine (`selectSize M`), and every wire is updated by at most 14 gates. -/
theorem size_stepCircuit_le [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs : List Bool) (T : ℕ) [NeZero T] (eW : Wire κ Q xs.length T ≃ Fin W)
    (eA : ActionBit κ Q ≃ Fin A) :
    (stepCircuit M xs T eW eA).size ≤ 6 * xs.length + 14 + selectSize M + 14 * W := by
  have : (updateCircuit xs T eW eA).size ≤ W * 14 :=
    size_ofTermsEquiv_le _ _ (numFuncs_updateTerm_le xs T)
  simp only [stepCircuit, readCircuit, selectCircuit, size_comp, size_ofTermsEquiv,
    Fintype.sum_sum_type, readTerm, selectTerm, Term.numFuncs_var, Finset.sum_const_zero,
    numFuncs_oneHot, numFuncs_ofBool, Fintype.sum_bool, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul, Term.numFuncs_relabel, selectSize]
  omega

/-- The initialization has one constant gate per wire. -/
theorem size_initCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs : List Bool) (T t : ℕ) (eW : Wire κ Q xs.length T ≃ Fin W) :
    (initCircuit M xs T t eW).size = W := by
  simp only [initCircuit, size_ofTermsEquiv, Fintype.sum_sum_type, initTerm, numFuncs_ofBool,
    Term.numFuncs_var, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero]
  exact (Fintype.card_congr eW).trans (Fintype.card_fin W)

/-- Acceptance reads the control state and the output cells. -/
theorem size_acceptCircuit_le [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (T : ℕ) (w : List Bool) (eW : Wire κ Q xs.length T ≃ Fin W) :
    (acceptCircuit M xs T w eW).size ≤ 3 * FinEnum.card Q + 6 * T + 3 := by
  simp only [acceptCircuit, size_ofTermsEquiv, Finset.univ_unique, Finset.sum_singleton, acceptTerm,
    numFuncs_inf, numFuncs_oneHot, numFuncs_ofBool, List.map_const', List.sum_replicate,
    FinEnum.length_toList, smul_eq_mul, apply_ite Term.numFuncs, numFuncs_bot]
  split_ifs
  · refine (Nat.add_le_add_right (Nat.add_le_add_left (numFuncs_listInf_le _ _ fun j _ ↦
      numFuncs_listInf_le _ _ fun v _ ↦ numFuncs_literal_le _ _) _) _).trans ?_
    simp only [List.length_finRange, List.length_cons, List.length_nil]
    omega
  · omega

end Size

end RunCircuit

/-! ### Bounded run circuit -/

open RunCircuit in
/-- A run of `t` steps on input `xs`, accepting when it has halted with output `w`. The inputs are
the `t` labels; each stack has `t + 1` cells, one more than the run can fill. -/
public def runCircuit [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
    (xs w : List Bool) (t : ℕ) : Circuit .booleanAlgebra t 1 :=
  (initCircuit M xs (t + 1) t FinEnum.equiv).comp
    (((stepCircuit M xs (t + 1) FinEnum.equiv FinEnum.equiv).unroll t).comp
      (acceptCircuit M xs (t + 1) w FinEnum.equiv))

open RunCircuit in
/-- The circuit checks whether the endpoint along the labels has halted with output `w`. -/
public theorem eval_runCircuit [FinEnum κ] [FinEnum Q]
    (M : StackMachine BinaryChoice κ Bool Q) (xs w : List Bool) (t : ℕ) (x : Fin t → Bool) :
    (runCircuit M xs w t).eval x 0 =
      let c := (List.ofFn (finTwoEquiv.symm ∘ x)).foldl M.stepAlong
        (M.init xs : Q × Cfg κ Bool xs.toArray)
      decide (M.Halted c ∧ c.2.output = w.toArray) := by
  simp only [runCircuit, Circuit.eval_comp, eval_initCircuit, Circuit.eval_unroll]
  rw [foldl_eval_stepCircuit M xs (t + 1) FinEnum.equiv FinEnum.equiv _ _
    (fun i ↦ by simp [List.length_ofFn])]
  simp only [acceptCircuit, Circuit.eval_ofTermsEquiv, Function.comp_apply,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, ← List.map_ofFn, List.foldl_map]
  rw [realize_acceptTerm]
  have := M.length_stack_foldl_stepAlong_le ((List.ofFn x).map finTwoEquiv.symm)
    (M.init xs : Q × Cfg κ Bool xs.toArray) none
  simp only [Controller.init_snd, hasConfig_init, Cfg.stack_init, List.length_nil, List.length_map,
    List.length_ofFn, Nat.zero_add, List.foldl_map] at this
  omega

/-- Some label sequence makes the circuit true exactly when some branch of the `t`-step run has
halted with output `w`. -/
public theorem exists_eval_runCircuit_iff [FinEnum κ] [FinEnum Q]
    (M : StackMachine BinaryChoice κ Bool Q) (xs w : List Bool) (t : ℕ) :
    (∃ x, (runCircuit M xs w t).eval x 0 = true) ↔
      ∃ c ∈ returns (M.runWith Multiset xs t), M.Halted c ∧ c.2.output = w.toArray := by
  simp only [eval_runCircuit, decide_eq_true_eq, Controller.mem_returns_runWith_multiset_iff]
  constructor
  · rintro ⟨x, h⟩
    exact ⟨_, ⟨finTwoEquiv.symm ∘ x, rfl⟩, h⟩
  · rintro ⟨_, ⟨bs, rfl⟩, h⟩
    refine ⟨finTwoEquiv ∘ bs, ?_⟩
    simpa [Function.comp_def] using h

open RunCircuit in
/-- For a fixed machine, the gate count of a `t`-step run circuit is
`O((t + 1) * (xs.length + t + 1))`, with one coefficient for all triples `(xs, w, t)` of an input,
a target output, and a step count. -/
public theorem dominated_size_runCircuit [FinEnum κ] [FinEnum Q]
    (M : StackMachine BinaryChoice κ Bool Q) :
    Dominated (fun p : List Bool × List Bool × ℕ ↦ (runCircuit M p.1 p.2.1 p.2.2).size)
      (fun p ↦ (p.2.2 + 1) * (p.1.length + p.2.2 + 1)) := by
  let N (p : List Bool × List Bool × ℕ) := p.1.length + p.2.2 + 1
  have hc (c : ℕ) : Dominated (fun _ ↦ c) N := .const_of_pos c fun _ ↦ Nat.succ_pos _
  have hL : Dominated (fun p ↦ p.1.length) N := .of_le fun _ ↦ Nat.le_succ_of_le le_self_add
  have hT : Dominated (fun p ↦ p.2.2 + 1) N := .of_le fun _ ↦ Nat.le_add_left _ _
  have hW : Dominated (fun p ↦ FinEnum.card (Wire κ Q p.1.length (p.2.2 + 1))) N := by
    simp only [card_wire, Dominated.add_iff, hc, hL, hT.const_mul_left, and_self]
  have h1 {f} (h : Dominated f N) : Dominated f (fun p ↦ (p.2.2 + 1) * N p) :=
    h.mono fun _ ↦ Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  simp only [runCircuit, Circuit.size_comp, Circuit.size_unroll, size_initCircuit,
    Dominated.add_iff]
  refine ⟨h1 hW, .mul (g' := N) (.of_le fun p ↦ Nat.le_succ p.2.2) ?_, h1 ?_⟩
  · refine .mono_left ?_ fun p ↦ size_stepCircuit_le M p.1 (p.2.2 + 1) _ _
    simp only [Dominated.add_iff, hc, hL.const_mul_left, hW.const_mul_left, and_self]
  · refine .mono_left ?_ fun p ↦ size_acceptCircuit_le M p.1 (p.2.2 + 1) p.2.1 _
    simp only [Dominated.add_iff, hc, hT.const_mul_left, and_self]

end Complexity.StackMachine
