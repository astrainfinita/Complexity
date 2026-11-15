/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Data.IntMemory.List
public import Complexity.Control.Controller.Simulation

/-!
# Simulating stacks by work tapes

Each stack occupies the positive addresses of one tape. A newly pushed top stays in finite
control until the next action; the remaining symbols are already on tape. This representation
is preserved by one target transition, with each head always at its source stack height. The
correspondence of histories (`Tape.HistRep`) holds for every choice shape and every interpretation
of the choices, and carries computations along (`ComputesInWith.toTM`).
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

/-- Simulate stack transitions with cached tops in finite control. Every choice is translated
separately, so the choice shape `F` is unchanged. -/
@[simps]
def toTM {F : Type → Type*} [Functor F] (M : StackMachine F κ Γ Q) :
    TM F κ (Option Γ) (ControlState κ Γ Q) where
  q₀ := (M.q₀, fun _ ↦ none)
  halt q := M.halt q.1
  transition q v :=
    (fun a ↦ ((a.1, fun i ↦ (a.2.work i).pending), a.2.toTM q.2 (q.observe v).2)) <$>
      M.transition q.1 (q.observe v)

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

theorem init_toTM {F : Type → Type*} [Functor F] (M : StackMachine F κ Γ Q) (xs : List Γ) :
    (((M.init xs).1, (M.init xs).2.cache fun _ ↦ false), (M.init xs).2.toTM fun _ ↦ false) =
      M.toTM.init (xs.map some) := by
  refine Prod.ext (Prod.ext rfl (funext fun _ ↦ rfl)) ?_
  apply TM.Cfg.ext <;> first | rfl | simp [funext_iff, Cfg.init, TM.Cfg.init]

/-- A stack history and a tape history of the same length: the last tape configuration encodes the
last stack configuration, with some tops kept in finite control, and each tape has visited
exactly the heights of its stack along the stack history. -/
structure Tape.HistRep (p : Controller.History (Q × Cfg κ Γ xs) (Q × Action κ Γ))
    (e : Controller.History
      (ControlState κ Γ Q × TM.Cfg κ (Option Γ) (xs.toList.map some).toArray)
      (ControlState κ Γ Q × TM.Action κ (Option Γ))) : Prop where
  last_eq : ∃ cached, e.last = ((p.last.1, p.last.2.cache cached), p.last.2.toTM cached)
  length_eq : e.length = p.length
  visited_eq : e.snd.visited = p.snd.configSup fun c i ↦ .pure ((c.stacks i).length : ℤ)

variable {p : Controller.History (Q × Cfg κ Γ xs) (Q × Action κ Γ)}
  {e : Controller.History (ControlState κ Γ Q × TM.Cfg κ (Option Γ) (xs.toList.map some).toArray)
    (ControlState κ Γ Q × TM.Action κ (Option Γ))}

/-- No simulated tape visits beyond the peak total number of live stack symbols. -/
theorem Tape.HistRep.space_le [Fintype κ] (h : Tape.HistRep p e) :
    e.snd.space ≤ Fintype.card κ * (p.snd.configSup Cfg.mass + 1) := by
  set s := p.snd.configSup Cfg.mass
  refine (Controller.History.space_le_of_visited_le _ (fun _ ↦ ⟨(0, s), Int.natCast_nonneg s⟩)
    ?_).trans (Finset.sum_const_nat fun _ _ ↦ by dsimp only; omega).le
  rw [h.visited_eq, Controller.History.configSup_le_iff]
  refine fun c hc i ↦ NonemptyInterval.le_def.mpr ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr ?_⟩
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
    (p.snd.config_le_configSup Cfg.mass hc)

section Interpreted

variable {F : Type → Type*} [Functor F] (m : Type → Type*) [Monad m] [LawfulMonad m]
  [MonadLiftT F m] [LawfulFunctorLiftT F m] (M : StackMachine F κ Γ Q)

/-- Each source step and the target step are images of the same choice, for every choice shape
`F` and every interpretation `m`; each target successor encodes its source successor, including
halted padding. -/
theorem Tape.HistRep.liftRel_stepWith (h : Tape.HistRep p e) :
    LiftRel Tape.HistRep (M.stepWith m p) (M.toTM.stepWith m e) := by
  obtain ⟨cached, he⟩ := h.last_eq
  have ht : (observe p.last.2 : Option Γ × (κ → Option Γ)).2 =
      fun i ↦ (p.last.2.stacks i).head? := rfl
  refine Controller.liftRel_stepWith_of_map m h (by simp [Controller.Halted, he])
    (fun a ↦ ((a.1, fun i ↦ (a.2.work i).pending),
      a.2.toTM (p.last.2.cache cached) fun i ↦ (p.last.2.stacks i).head?))
    (by simp only [toTM_transition, Controller.History.state_def,
      Controller.History.observe_def, he, Controller.state_prod, Controller.observe_prod,
      Cfg.observe_toTM, ht]) fun a ↦ ?_
  refine ⟨⟨fun i ↦ (a.2.work i).pending.isSome, ?_⟩,
    by simp [Controller.History.apply_def, h.length_eq], ?_⟩
  · simp only [Controller.History.apply_last, he, Controller.apply_prod, Action.apply_toTM,
      Action.cache_apply]
  · rw [Controller.History.snd_apply, Controller.History.snd_apply,
      Controller.History.visited_snoc, h.visited_eq, Controller.History.configSup_snoc,
      Controller.History.last_snd, Controller.History.last_snd, he]
    simp only [Action.apply_toTM, Cfg.toTM_workPos]

/-- Bounded runs preserve the encoding for every choice shape and interpretation, and each target
history visits on every tape exactly the heights of the corresponding stack in its own source
history. With `m = Multiset`, every stack branch corresponds to exactly one tape branch,
retaining multiplicities (`LiftRel.multisetRel`). -/
theorem liftRel_runHistoryWith_toTM (xs : List Γ) (n : ℕ) :
    LiftRel Tape.HistRep (M.runHistoryWith m xs n) (M.toTM.runHistoryWith m (xs.map some) n) := by
  rw [Controller.runHistoryWith, Controller.runHistoryWith, ← init_toTM]
  exact Controller.liftRel_runFromWith m M M.toTM (fun _ _ h ↦ h.liftRel_stepWith m M)
    ⟨⟨_, rfl⟩, rfl, by simp⟩ n

variable {m} [MonadReturns m] {M}

/-- Simulation passes a computation along, for every choice shape and every interpretation: it
preserves time and bounds every tape by the source peak stack space, including the blank bottom
cell. On `Multiset` the outputs of the branches correspond with their multiplicities. -/
theorem _root_.Complexity.Controller.ComputesInWith.toTM [Fintype κ] {xs : List Γ}
    {outs : m (List Γ)} {t s : ℕ}
    (h : M.ComputesInWith m xs outs Controller.History.length
      (fun h ↦ h.configSup Cfg.mass) t s) :
    M.toTM.ComputesInWith m (xs.map some) ((·.map some) <$> outs)
      Controller.History.length Controller.History.space t (Fintype.card κ * (s + 1)) :=
  h.of_liftRel (liftRel_runHistoryWith_toTM m M xs) (fun c ↦ c.2.output.toList)
    (fun _ _ _ ↦ by simp_all)
    (fun _ _ hr hb ↦ ⟨by simpa only [Controller.History.length_snd, hr.length_eq] using hb.1,
      hr.space_le.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hb.2))⟩)
    (fun _ _ hr hp ↦ by obtain ⟨_, he⟩ := hr.last_eq; simpa [Controller.Halted, he] using hp)
    (fun _ _ _ hr _ ↦ by obtain ⟨_, he⟩ := hr.last_eq; simp_all)

end Interpreted

/-- Simulation preserves time and bounds every tape by the source peak stack space,
including the blank bottom cell. -/
theorem ComputesWithin.toTM [Fintype κ] {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.toTM.ComputesWithin (xs.map some) (ys.map some)
      t (Fintype.card κ * (s + 1)) :=
  Controller.ComputesInWith.toTM h

end Complexity.StackMachine
