/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Data.IntMemory.List

/-!
# Simulating stacks by work tapes

Each stack occupies the positive addresses of one tape, with its top under the head.
Address zero is blank and represents the empty stack. Each source transition uses exactly
two target transitions: move for pushes and erase/move for pops, then write pushed symbols.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {κ Γ Q Q' : Type} {xs : Array Γ}

namespace Tape

@[simp] private theorem option_default : (default : Option Γ) = none := rfl

/-- The blank bottom marker, followed by symbols from the bottom to the top. -/
def cells (s : List Γ) : List (Option Γ) := none :: s.reverse.map some

/-- Place a stack in positive tape cells, with a blank bottom boundary. -/
def encode (s : List Γ) : IntMemory (Option Γ) := IntMemory.ofList (cells s)

@[simp] theorem cells_length (s : List Γ) : (cells s).length = s.length + 1 := by
  simp [cells]

@[simp] theorem cells_cons (a : Γ) (s : List Γ) :
    cells (a :: s) = cells s ++ [some a] := by simp [cells]

@[simp] theorem encode_nil : encode ([] : List Γ) = ∅ := by
  exact IntMemory.ofList_append_default []

@[simp] theorem top (s : List Γ) : (encode s).nonneg[s.length] = s.head? := by
  cases s with
  | nil => simp
  | cons a s =>
    simp [encode]

@[simp] theorem push (a : Γ) (s : List Γ) :
    (encode s).set (s.length + 1) (some a) = encode (a :: s) := by
  simpa [encode] using IntMemory.set_ofList_length (cells s) (some a)

@[simp] theorem pop (a : Γ) (s : List Γ) :
    (encode (a :: s)).set (s.length + 1) none = encode s := by
  simpa [encode] using IntMemory.set_ofList_append_length (cells s) (some a)

end Tape

/-- Encode all stacks while selecting an arbitrary target control state. -/
@[simps]
def Cfg.toTM (c : Cfg κ Γ Q xs) (q : Q') : TM.Cfg κ (Option Γ) Q' (xs.toList.map some).toArray where
  state := q
  inputPos := ⟨c.inputPos.val, by simp⟩
  workTapes i := Tape.encode (c.stacks i)
  workPos i := (c.stacks i).length
  output := c.output.map some

theorem Cfg.observe_toTM (c : Cfg κ Γ Q xs) (q : Q') :
    observe (c.toTM q) = (observe c : Option Γ × (κ → Option Γ)) := by
  apply Prod.ext
  · cases h : c.inputPos.val with
    | zero => simp [TM.Cfg.inputSymbol, h]
    | succ n => simp [TM.Cfg.inputSymbol, h]; cases xs[n]? <;> rfl
  · funext i
    exact Tape.top (c.stacks i)

/-- The second phase remembers just the symbols to push and the next source label. -/
abbrev ControlState (κ Γ Q : Type) := Q ⊕ ((κ → Option Γ) × Q)

/-- A pushed symbol awaits the second target transition. -/
def Op.pending : Op Γ → Option Γ
  | .push a => some a
  | _ => none

/-- The first phase performs input/output and the movements/erasures on work tapes. -/
@[simps]
def Action.first (a : Action κ Γ Q) (top : κ → Option Γ) :
    TM.Action κ (Option Γ) (ControlState κ Γ Q) where
  inputMove := a.inputMove
  work i := match a.work i with
    | .nop => (none, 0)
    | .push _ => (none, 1)
    | .pop => match top i with
      | none => (none, 0)
      | some _ => (some none, -1)
  output := a.output.map some
  state := .inr (fun i ↦ (a.work i).pending, a.state)

/-- The second phase writes the pushed symbols without moving any heads. -/
@[simps]
def Action.second (pending : κ → Option Γ) (q : Q) :
    TM.Action κ (Option Γ) (ControlState κ Γ Q) where
  inputMove := 0
  work i := ((pending i).map some, 0)
  output := none
  state := .inl q

/-- Simulate each stack transition with two work-tape transitions. -/
@[simps]
def toTM (M : StackMachine Id κ Γ Q) : TM Id κ (Option Γ) (ControlState κ Γ Q) where
  q₀ := .inl M.q₀
  halt := fun q ↦ match q with
    | .inl q => M.halt q
    | .inr _ => false
  transition q v := pure <| match q with
    | .inl q => ((M.transition q v).run).first v.2
    | .inr (pending, q') => Action.second pending q'

/-- Both target phases implement one simultaneous source action. -/
theorem Action.apply_toTM (a : Action κ Γ Q) (c : Cfg κ Γ Q xs) :
    apply (Action.second (fun i ↦ (a.work i).pending) a.state)
      (apply (a.first (fun i ↦ (c.stacks i).head?))
        (c.toTM (Sum.inl c.state : ControlState κ Γ Q))) =
      (apply a c).toTM (Sum.inl a.state : ControlState κ Γ Q) := by
  apply TM.Cfg.ext
  · rfl
  · apply Fin.ext
    cases h : a.inputMove <;> simp [h, Input.movePos]
  · funext i
    cases h : a.work i with
    | nop | push _ => simp [Op.pending, Op.apply, h]
    | pop => cases hs : c.stacks i <;> simp [Op.pending, Op.apply, h, hs]
  · funext i
    cases h : a.work i <;> cases hs : c.stacks i <;>
      simp [Op.pending, Op.apply, h, hs, SignType.cast]
  · cases h : a.output <;> simp [h]

/-- Two target steps implement one source step, including halted padding. -/
theorem runFrom_two_toTM (M : StackMachine Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    M.toTM.runFrom (c.toTM (.inl c.state)) 2 =
      (M.step c).toTM (.inl (M.step c).state) := by
  by_cases h : M.Halted c
  · have ht : M.toTM.Halted (c.toTM (.inl c.state)) := h
    rw [Controller.runFrom_of_halted _ _ ht, Controller.step_of_halted _ _ h]
  · simpa [-TM.Cfg.observe_def, Controller.runFrom_succ, Controller.step_eq,
      Cfg.observe_toTM, show M.halt c.state = false from Bool.eq_false_iff.mpr h]
      using Action.apply_toTM ((M.transition c.state (observe c)).run) c

/-- Every bounded stack execution has the same result after twice as many target steps. -/
theorem runFrom_toTM (M : StackMachine Id κ Γ Q) (c : Cfg κ Γ Q xs) (n : ℕ) :
    M.toTM.runFrom (c.toTM (.inl c.state)) (2 * n) =
      (M.runFrom c n).toTM (.inl (M.runFrom c n).state) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm, Controller.runFrom_add,
      runFrom_two_toTM, ih, Controller.runFrom_succ]

theorem init_toTM (xs : List Γ) (q : Q) :
    ((execution (κ := κ) xs).init q).toTM (.inl q : ControlState κ Γ Q) =
      (TM.rawExecution (xs.map some)).init (.inl q) := by
  apply TM.Cfg.ext <;> first | rfl | simp [funext_iff]

/-- The target run preserves the input/output convention of the source run. -/
theorem run_toTM (M : StackMachine Id κ Γ Q) (xs : List Γ) (n : ℕ) :
    M.toTM.run (TM.Cfg κ (Option Γ) (ControlState κ Γ Q) (xs.map some).toArray)
      (xs.map some) (2 * n) =
      (M.run (Cfg κ Γ Q xs.toArray) xs n).toTM
        (.inl (M.run (Cfg κ Γ Q xs.toArray) xs n).state) := by
  change M.toTM.runFrom ((TM.rawExecution (xs.map some)).init (.inl M.q₀)) _ = _
  rw [← init_toTM]
  exact M.runFrom_toTM (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) n

/-- A stack computation yields a TM computation. This bound uses elapsed time;
it does not claim to preserve the maximum number of live stack symbols. -/
theorem ComputesInTimeAndSpace.toTM [Fintype κ] {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesInTimeAndSpace xs ys t s) :
    M.toTM.ComputesInTimeAndSpace (xs.map some) (ys.map some)
      (2 * t) (Fintype.card κ * (2 * t + 1)) := by
  obtain ⟨hh, ho⟩ := h.run_spec
  apply Controller.computes_unit_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [run_toTM, Controller.Halted, TM.Cfg.state_def, Cfg.toTM_state,
      toTM_halt, state_def] using hh
  · simpa only [TM.rawExecution_hasOutput, run_toTM, Cfg.toTM_output,
      List.map_toArray] using congrArg (Array.map some) ho
  · exact (Controller.History.space_le_length _).trans
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ (M.toTM.runHistory_spec _ _ (2 * t)).length_le))

end Complexity.StackMachine
