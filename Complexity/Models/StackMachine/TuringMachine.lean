/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Data.IntMemory.List
public import Complexity.Control.Transition.Simulation

/-!
# Simulating stacks by work tapes

Each stack occupies the positive addresses of one tape. A newly pushed top stays in finite
control until the next action; the remaining symbols are already on tape. This representation
is preserved by one target transition, with each head always at its source stack height.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {κ Γ Q : Type} {xs : Array Γ}

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

@[simp] theorem erase_above (s : List Γ) :
    (encode s).set (s.length + 1) none = encode s := by
  have h := IntMemory.ofList_append_default (cells s)
  rw [← IntMemory.set_ofList_length] at h
  simpa [encode] using h

end Tape

/-- The control remembers a pushed top until the next action writes or discards it. -/
abbrev ControlState (κ Γ Q : Type) := Q × (κ → Option Γ)

/-- Encode a configuration, optionally keeping each top in finite control. -/
@[simps state_fst state_snd inputPos_val workTapes workPos output]
def Cfg.toTM (c : Cfg κ Γ Q xs) (cached : κ → Bool) :
    TM.Cfg κ (Option Γ) (ControlState κ Γ Q) (xs.toList.map some).toArray where
  state := (c.state, fun i ↦ if cached i then (c.stacks i).head? else none)
  inputPos := ⟨c.inputPos.val, by simp⟩
  workTapes i := Tape.encode (if cached i then (c.stacks i).tail else c.stacks i)
  workPos i := (c.stacks i).length
  output := c.output.map some

/-- Cached symbols take precedence over the tape under the head. -/
def ControlState.observe (q : ControlState κ Γ Q) (v : Option Γ × (κ → Option Γ)) :
    Option Γ × (κ → Option Γ) := (v.1, fun i ↦ (q.2 i).or (v.2 i))

theorem Cfg.observe_toTM (c : Cfg κ Γ Q xs) (cached : κ → Bool) :
    (c.toTM cached).state.observe (observe (c.toTM cached)) = observe c := by
  apply Prod.ext
  · cases h : c.inputPos.val with
    | zero => simp [ControlState.observe, TM.Cfg.inputSymbol, h]
    | succ n => simp [ControlState.observe, TM.Cfg.inputSymbol, h]; cases xs[n]? <;> rfl
  · funext i
    cases hc : cached i with
    | false => simp [ControlState.observe, TM.Cfg.workSymbols, hc]
    | true => cases hs : c.stacks i <;> simp [ControlState.observe, TM.Cfg.workSymbols, hc, hs]

/-- A pushed symbol is the only pending write after an action. -/
def Op.pending : Op Γ → Option Γ
  | .push a => some a
  | _ => none

/-- Write an old cached top before moving for a push; a pop discards it instead. -/
@[simps]
def Action.toTM (a : Action κ Γ Q) (pending top : κ → Option Γ) :
    TM.Action κ (Option Γ) (ControlState κ Γ Q) where
  inputMove := a.inputMove
  work i := match a.work i with
    | .nop => ((pending i).map some, 0)
    | .push _ => ((pending i).map some, 1)
    | .pop => match top i with
      | none => (none, 0)
      | some _ => (some none, -1)
  output := a.output.map some
  state := (a.state, fun i ↦ (a.work i).pending)

/-- Simulate stack transitions with cached tops in finite control. -/
@[simps]
def toTM (M : StackMachine Id κ Γ Q) : TM Id κ (Option Γ) (ControlState κ Γ Q) where
  q₀ := (M.q₀, fun _ ↦ none)
  halt q := M.halt q.1
  transition q v := pure <|
    ((M.transition q.1 (q.observe v)).run).toTM q.2 (q.observe v).2

/-- One target action preserves the encoding, caching precisely the newly pushed tops. -/
theorem Action.apply_toTM (a : Action κ Γ Q) (c : Cfg κ Γ Q xs) (cached : κ → Bool) :
    apply (a.toTM (c.toTM cached).state.2 (fun i ↦ (c.stacks i).head?)) (c.toTM cached) =
      (apply a c).toTM (fun i ↦ (a.work i).pending.isSome) := by
  apply TM.Cfg.ext
  · apply Prod.ext
    · rfl
    · funext i; cases h : a.work i <;> simp [Op.pending, Op.apply, h]
  · apply Fin.ext
    cases h : a.inputMove <;> simp [h, Input.movePos]
  · funext i
    cases h : a.work i <;> cases hc : cached i <;> cases hs : c.stacks i <;>
      simp [Op.pending, Op.apply, h, hc, hs]
  · funext i
    cases h : a.work i <;> cases hs : c.stacks i <;>
      simp [Op.pending, Op.apply, h, hs, SignType.cast]
  · cases h : a.output <;> simp [h]

/-- A source step has an encoded target successor, including halted padding. -/
theorem step_toTM (M : StackMachine Id κ Γ Q) (c : Cfg κ Γ Q xs) (cached : κ → Bool) :
    ∃ cached', M.toTM.step (c.toTM cached) = (M.step c).toTM cached' := by
  by_cases h : M.Halted c
  · have ht : M.toTM.Halted (c.toTM cached) := h
    exact ⟨cached, by rw [M.toTM.step_of_halted _ ht, M.step_of_halted _ h]⟩
  · refine ⟨fun i ↦ (((M.transition c.state (observe c)).run).work i).pending.isSome, ?_⟩
    simpa [-TM.Cfg.observe_def, Controller.step_eq, ↓Cfg.observe_toTM,
      show M.halt c.state = false from Bool.eq_false_iff.mpr h]
      using Action.apply_toTM ((M.transition c.state (observe c)).run) c cached

/-- Bounded runs preserve the encoding without exposing the cache bookkeeping. -/
theorem runFrom_toTM (M : StackMachine Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (cached : κ → Bool) (n : ℕ) :
    ∃ cached', M.toTM.runFrom (c.toTM cached) n = (M.runFrom c n).toTM cached' :=
  Transition.rel_runN (f := M.step) (g := M.toTM.step)
    (R := fun (c : Cfg κ Γ Q xs) d ↦ ∃ cached, d = c.toTM cached)
    (by rintro c _ ⟨cached, rfl⟩; exact M.step_toTM c cached) ⟨cached, rfl⟩ n

/-- No simulated tape visits beyond the peak total number of live stack symbols. -/
theorem space_runHistoryFrom_toTM_le [Fintype κ] (M : StackMachine Id κ Γ Q)
    (c : Cfg κ Γ Q xs) (cached : κ → Bool) (n : ℕ) :
    (M.toTM.runHistoryFrom (c.toTM cached) n).space ≤
      Fintype.card κ * ((M.runHistoryFrom c n).configSup Cfg.mass + 1) := by
  let s := (M.runHistoryFrom c n).configSup Cfg.mass
  let v : NonemptyInterval ℤ := ⟨(0, s), by omega⟩
  have hv : (M.toTM.runHistoryFrom (c.toTM cached) n).visited ≤ fun _ ↦ v := by
    intro i
    apply (M.toTM.runHistoryFrom_visited_le_iff _ _ i v).mpr
    intro m hm
    obtain ⟨cached', hc⟩ := M.runFrom_toTM c cached m
    rw [hc, Cfg.toTM_workPos]
    have hi : ((M.runFrom c m).stacks i).length ≤ s :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
        (M.config_le_configSup_runHistoryFrom Cfg.mass c hm)
    change 0 ≤ _ ∧ _ ≤ (s : ℤ)
    exact ⟨by omega, by exact_mod_cast hi⟩
  simpa [v] using Controller.History.space_le_of_visited_le _ (fun _ ↦ v) hv

theorem init_toTM (xs : List Γ) (q : Q) :
    ((execution (κ := κ) xs).init q).toTM (fun _ ↦ false) =
      (TM.rawExecution (xs.map some)).init (q, fun _ ↦ none) := by
  apply TM.Cfg.ext <;> first | rfl | simp [funext_iff]

/-- The target run preserves the input/output convention of the source run. -/
theorem run_toTM (M : StackMachine Id κ Γ Q) (xs : List Γ) (n : ℕ) :
    ∃ cached, M.toTM.run (TM.Cfg κ (Option Γ) (ControlState κ Γ Q) (xs.map some).toArray)
      (xs.map some) n = (M.run (Cfg κ Γ Q xs.toArray) xs n).toTM cached := by
  change ∃ cached, M.toTM.runFrom
    ((TM.rawExecution (xs.map some)).init (M.q₀, fun _ ↦ none)) _ = _
  rw [← init_toTM]
  exact M.runFrom_toTM (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) (fun _ ↦ false) n

/-- Simulation preserves time and bounds every tape by the source peak stack space,
including the blank bottom cell. -/
theorem ComputesWithin.toTM [Fintype κ] {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.toTM.ComputesWithin (xs.map some) (ys.map some)
      t (Fintype.card κ * (s + 1)) := by
  obtain ⟨hh, ho, hs⟩ := Controller.computesWith_unit_iff.mp h
  obtain ⟨cached, hr⟩ := M.run_toTM xs t
  apply Controller.computesWith_unit_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr, Controller.Halted, TM.Cfg.state_def, Cfg.toTM_state_fst,
      toTM_halt, state_def] using hh
  · simpa only [TM.rawExecution_hasOutput, hr, Cfg.toTM_output,
      List.map_toArray] using congrArg (Array.map some) ho
  · have hv := M.space_runHistoryFrom_toTM_le ((execution xs).init M.q₀) (fun _ ↦ false) t
    simp only [init_toTM] at hv
    exact hv.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hs))

end Complexity.StackMachine
