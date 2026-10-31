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

/-- Encode the storage of a configuration, optionally keeping each top in finite control. -/
@[simps inputPos_val workTapes workPos output]
def Cfg.toTM (c : Cfg κ Γ xs) (cached : κ → Bool) :
    TM.Cfg κ (Option Γ) (xs.toList.map some).toArray where
  inputPos := ⟨c.inputPos.val, by simp⟩
  workTapes i := Tape.encode (if cached i then (c.stacks i).tail else c.stacks i)
  workPos i := (c.stacks i).length
  output := c.output.map some

/-- The tops kept in finite control. -/
def Cfg.cache (c : Cfg κ Γ xs) (cached : κ → Bool) (i : κ) : Option Γ :=
  if cached i then (c.stacks i).head? else none

/-- Cached symbols take precedence over the tape under the head. -/
def ControlState.observe (q : ControlState κ Γ Q) (v : Option Γ × (κ → Option Γ)) :
    Option Γ × (κ → Option Γ) := (v.1, fun i ↦ (q.2 i).or (v.2 i))

theorem Cfg.observe_toTM (q : Q) (c : Cfg κ Γ xs) (cached : κ → Bool) :
    ControlState.observe (q, c.cache cached) (observe (c.toTM cached)) = observe c := by
  apply Prod.ext
  · cases h : c.inputPos.val with
    | zero => simp [ControlState.observe, TM.Cfg.inputSymbol, h]
    | succ n => simp [ControlState.observe, TM.Cfg.inputSymbol, h]; cases xs[n]? <;> rfl
  · funext i
    cases hc : cached i with
    | false => simp [ControlState.observe, TM.Cfg.workSymbols, Cfg.cache, hc]
    | true =>
      cases hs : c.stacks i <;>
        simp [ControlState.observe, TM.Cfg.workSymbols, Cfg.cache, hc, hs]

/-- A pushed symbol is the only pending write after an action. -/
def Op.pending : Op Γ → Option Γ
  | .push a => some a
  | _ => none

/-- Write an old cached top before moving for a push; a pop discards it instead. -/
@[simps]
def Action.toTM (a : Action κ Γ) (pending top : κ → Option Γ) : TM.Action κ (Option Γ) where
  inputMove := a.inputMove
  work i := match a.work i with
    | .nop => ((pending i).map some, 0)
    | .push _ => ((pending i).map some, 1)
    | .pop => match top i with
      | none => (none, 0)
      | some _ => (some none, -1)
  output := a.output.map some

/-- Simulate stack transitions with cached tops in finite control. -/
@[simps]
def toTM (M : StackMachine Id κ Γ Q) : TM Id κ (Option Γ) (ControlState κ Γ Q) where
  q₀ := (M.q₀, fun _ ↦ none)
  halt q := M.halt q.1
  transition q v := pure <|
    let a := (M.transition q.1 (q.observe v)).run
    ((a.1, fun i ↦ (a.2.work i).pending), a.2.toTM q.2 (q.observe v).2)

/-- One target action preserves the encoding, caching precisely the newly pushed tops. -/
theorem Action.apply_toTM (a : Action κ Γ) (c : Cfg κ Γ xs) (cached : κ → Bool) :
    apply (a.toTM (c.cache cached) (fun i ↦ (c.stacks i).head?)) (c.toTM cached) =
      (apply a c).toTM (fun i ↦ (a.work i).pending.isSome) := by
  apply TM.Cfg.ext
  · apply Fin.ext
    cases h : a.inputMove <;> simp [h, Input.movePos]
  · funext i
    cases h : a.work i <;> cases hc : cached i <;> cases hs : c.stacks i <;>
      simp [Op.pending, Op.apply, Cfg.cache, h, hc, hs]
  · funext i
    cases h : a.work i <;> cases hs : c.stacks i <;>
      simp [Op.pending, Op.apply, h, hs, SignType.cast]
  · cases h : a.output <;> simp [h]

/-- The tops cached after an action are exactly its pushed symbols. -/
theorem Action.cache_apply (a : Action κ Γ) (c : Cfg κ Γ xs) :
    (apply a c).cache (fun i ↦ (a.work i).pending.isSome) = fun i ↦ (a.work i).pending := by
  funext i
  cases h : a.work i <;> simp [Cfg.cache, Op.pending, Op.apply, h]

/-- A source step has an encoded target successor, including halted padding. -/
theorem step_toTM (M : StackMachine Id κ Γ Q) (c : Q × Cfg κ Γ xs) (cached : κ → Bool) :
    ∃ cached', M.toTM.step ((c.1, c.2.cache cached), c.2.toTM cached) =
      (((M.step c).1, (M.step c).2.cache cached'), (M.step c).2.toTM cached') := by
  by_cases h : M.Halted c
  · have ht : M.toTM.Halted ((c.1, c.2.cache cached), c.2.toTM cached) := h
    exact ⟨cached, by rw [M.toTM.step_of_halted _ ht, M.step_of_halted _ h]⟩
  · refine ⟨fun i ↦ (((M.transition c.1 (observe c.2)).run.2).work i).pending.isSome, ?_⟩
    rw [M.toTM.step_of_not_halted ((c.1, c.2.cache cached), c.2.toTM cached) h,
      M.step_of_not_halted _ h]
    have ht : (observe c.2 : Option Γ × (κ → Option Γ)).2 = fun i ↦ (c.2.stacks i).head? := rfl
    simp only [toTM_transition, Controller.state_prod, Controller.observe_prod, Id.run_pure,
      Controller.apply_prod, Cfg.observe_toTM, ht, Action.apply_toTM, Action.cache_apply]

/-- Bounded runs preserve the encoding without exposing the cache bookkeeping. -/
theorem runFrom_toTM (M : StackMachine Id κ Γ Q) (c : Q × Cfg κ Γ xs)
    (cached : κ → Bool) (n : ℕ) :
    ∃ cached', M.toTM.runFrom ((c.1, c.2.cache cached), c.2.toTM cached) n =
      (((M.runFrom c n).1, (M.runFrom c n).2.cache cached'), (M.runFrom c n).2.toTM cached') :=
  Transition.rel_runN
    (R := fun (c : Q × Cfg κ Γ xs) d ↦ ∃ cached, d = ((c.1, c.2.cache cached), c.2.toTM cached))
    (by rintro c _ ⟨cached, rfl⟩; exact M.step_toTM c cached) ⟨cached, rfl⟩ n

/-- No simulated tape visits beyond the peak total number of live stack symbols. -/
theorem space_runHistoryFrom_toTM_le [Fintype κ] (M : StackMachine Id κ Γ Q)
    (c : Q × Cfg κ Γ xs) (cached : κ → Bool) (n : ℕ) :
    (M.toTM.runHistoryFrom ((c.1, c.2.cache cached), c.2.toTM cached) n).snd.space ≤
      Fintype.card κ * ((M.runHistoryFrom c n).snd.configSup Cfg.mass + 1) := by
  let s := (M.runHistoryFrom c n).snd.configSup Cfg.mass
  let v : NonemptyInterval ℤ := ⟨(0, s), by omega⟩
  have hv : (M.toTM.runHistoryFrom ((c.1, c.2.cache cached), c.2.toTM cached) n).snd.visited ≤
      fun _ ↦ v := by
    intro i
    apply (M.toTM.runHistoryFrom_visited_le_iff _ _ i v).mpr
    intro m hm
    obtain ⟨cached', hc⟩ := M.runFrom_toTM c cached m
    rw [hc, Cfg.toTM_workPos]
    have hi : ((M.runFrom c m).2.stacks i).length ≤ s :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
        ((M.config_le_configSup_runHistoryFrom (Cfg.mass ∘ Prod.snd) c hm).trans_eq
          (Controller.History.configSup_snd _ _).symm)
    change 0 ≤ _ ∧ _ ≤ (s : ℤ)
    exact ⟨by omega, by exact_mod_cast hi⟩
  change _ ≤ Fintype.card κ * (s + 1)
  simpa [v] using Controller.History.space_le_of_visited_le _ (fun _ ↦ v) hv

theorem init_toTM (M : StackMachine Id κ Γ Q) (xs : List Γ) :
    (((M.init xs).1, (M.init xs).2.cache fun _ ↦ false), (M.init xs).2.toTM fun _ ↦ false) =
      M.toTM.init (xs.map some) := by
  refine Prod.ext (Prod.ext rfl (funext fun _ ↦ rfl)) ?_
  apply TM.Cfg.ext <;> first | rfl | simp [funext_iff, Cfg.init, TM.Cfg.init]

/-- The target run preserves the input/output convention of the source run. -/
theorem run_toTM (M : StackMachine Id κ Γ Q) (xs : List Γ) (n : ℕ) :
    ∃ cached, M.toTM.run (xs.map some) n =
      (((M.run xs n).1, (M.run xs n).2.cache cached), (M.run xs n).2.toTM cached) := by
  change ∃ cached, M.toTM.runFrom (M.toTM.init (xs.map some)) _ = _
  rw [← init_toTM]
  exact M.runFrom_toTM (M.init xs) (fun _ ↦ false) n

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
  · simpa only [hr, Controller.Halted, Controller.state_prod, toTM_halt] using hh
  · simpa only [TM.hasOutput_isOutput, hr, Cfg.toTM_output,
      List.map_toArray] using congrArg (Array.map some) ho
  · have hv := M.space_runHistoryFrom_toTM_le (M.init xs) (fun _ ↦ false) t
    rw [init_toTM] at hv
    exact hv.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hs))

end Complexity.StackMachine
