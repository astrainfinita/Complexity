/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Control.Transition.Simulation
public import Complexity.Models.TuringMachine.Tapes
public import Mathlib.Data.Fintype.Sum
public import Complexity.Data.IntMemory.List

/-! # Redirecting output to a work tape

An embedding places the source work tapes and their output buffer in the target bank.
Output is written starting at zero, with its head immediately after the written prefix.
Every source transition is one target transition. The target's external output and all other
unassigned tapes are preserved.
-/

@[expose] public section

namespace Complexity.TM.RedirectOutput

variable {Γ Q : Type*}

section Layout

variable {κ τ : Type*} [Fintype κ] [DecidableEq τ]

/-- Route the source work bank and its output buffer through one embedding. -/
@[simps]
def actionAlong (e : (κ ⊕ Unit) ↪ τ) (a : Action κ Γ Q) : Action τ Γ Q where
  inputMove := a.inputMove
  work := e.replace (Sum.elim a.work (fun _ ↦
    (a.output, if a.output.isSome then 1 else 0))) (fun _ ↦ (none, 0))
  output := none
  state := a.state

/-- Compile output redirection; injectivity separates the buffer from source work tapes. -/
@[simps]
def compilerAlong (e : (κ ⊕ Unit) ↪ τ) (M : TM Id κ Γ Q) : TM Id τ Γ Q where
  q₀ := M.q₀
  halt := M.halt
  transition := fun q (a, v) ↦ pure <|
    actionAlong e ((M.transition q (a, v ∘ (Function.Embedding.inl.trans e))).run)

variable {Δ : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Install the source work bank and output buffer, preserving the caller's other fields. -/
@[simps]
def cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) : Cfg τ Γ Q xs where
  state := c.state
  inputPos := c.inputPos
  workTapes := e.replace (Sum.elim c.workTapes (fun _ ↦ IntMemory.ofArray c.output)) d.workTapes
  workPos := e.replace (Sum.elim c.workPos (fun _ ↦ c.output.size)) d.workPos
  output := d.output

private theorem set_ofArray_size (ys : Array Γ) (a : Γ) :
    (IntMemory.ofArray ys).set ys.size a = IntMemory.ofArray (ys.push a) := by
  have h := IntMemory.set_ofList_length ys.toList a
  rw [← Array.toList_push] at h
  simpa only [IntMemory.ofList, Array.toArray_toList, Array.length_toList] using h

/-- Output redirection commutes with applying an action. -/
theorem apply_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (a : Action κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) :
    apply (actionAlong e a) (cfgAlong e c d) =
      cfgAlong e (apply a c) d := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      rcases j with j | ⟨⟩
      · simp
      · cases ha : a.output <;>
          simp [ha, set_ofArray_size]
    · simp [hj]
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      rcases j with j | ⟨⟩
      · simp
      · cases ha : a.output <;> simp [ha]
    · simp [hj]
  · rfl

/-- Output redirection simulates one source step exactly. -/
theorem step_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) :
    (compilerAlong e M).step (cfgAlong e c d) = cfgAlong e (M.step c) d := by
  have hv : (cfgAlong e c d).workSymbols ∘ (Function.Embedding.inl.trans e) =
      c.workSymbols := by
    funext j
    simp [Function.comp_def, Cfg.workSymbols]
  by_cases hh : M.halt c.state = true
  · simp only [TM.step_eq, compilerAlong_halt, cfgAlong_state, hh, ite_true]
  · simp only [TM.step_eq]
    change (if M.halt c.state then _ else _) = _
    simp only [hh]
    change apply (actionAlong e ((M.transition c.state
      (c.inputSymbol, (cfgAlong e c d).workSymbols ∘ (Function.Embedding.inl.trans e))).run)) _ = _
    rw [hv, apply_cfgAlong]
    rfl

/-- The embedding preserves a bounded run and all its untouched tapes. -/
theorem runFrom_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ) :
    (compilerAlong e M).runFrom (cfgAlong e c d) n =
      cfgAlong e (M.runFrom c n) d :=
  Transition.runN_map (fun c ↦ cfgAlong e c d) (fun c ↦ step_cfgAlong e M c d) c n

/-- The original work tapes record the same intervals after embedding. -/
theorem visited_embed (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ) (j : κ) :
    ((compilerAlong e M).runHistoryFrom (cfgAlong e c d) n).visited (e (.inl j)) =
      (M.runHistoryFrom c n).visited j := by
  apply TM.runHistoryFrom_visited_congr
  intro m _
  simp [runFrom_cfgAlong]

/-- The output buffer stays between its starting and ending output lengths. -/
theorem visited_self_le (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ) :
    ((compilerAlong e M).runHistoryFrom (cfgAlong e c d) n).visited (e (.inr ())) ≤
      ⟨(c.output.size, (M.runFrom c n).output.size),
        Int.ofNat_le.mpr (M.output_size_le_runFrom c n)⟩ := by
  apply (TM.runHistoryFrom_visited_le_iff _ _ _ _ _).mpr
  intro m hm
  simp only [runFrom_cfgAlong, cfgAlong_workPos, Function.Embedding.replace_apply,
    Sum.elim_inr, NonemptyInterval.mem_mk]
  exact ⟨by exact_mod_cast M.output_size_le_runFrom c m,
    by exact_mod_cast M.output_size_runFrom_mono c hm⟩

/-- Heads outside the embedding retain singleton visit intervals. -/
theorem visited_extra (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ)
    (j : τ) (hj : j ∉ Set.range e) :
    ((compilerAlong e M).runHistoryFrom (cfgAlong e c d) n).visited j =
      NonemptyInterval.pure (d.workPos j) := by
  apply le_antisymm
  · apply (TM.runHistoryFrom_visited_le_iff _ _ _ _ _).mpr
    intro m _
    simp [runFrom_cfgAlong, hj]
  · change d.workPos j ∈ ((compilerAlong e M).runHistoryFrom (cfgAlong e c d) n).visited j
    have h := ((compilerAlong e M).runHistoryFrom (cfgAlong e c d) n).first_head_mem j
    simpa only [Controller.first_runHistoryFrom, cfgAlong_workPos,
      Function.Embedding.replace_of_not_mem _ _ _ hj] using h

@[simp↓]
theorem cfg_init (e : (κ ⊕ Unit) ↪ τ) (xs : List Γ) (q : Q) :
    cfgAlong e ((rawExecution xs).init q) ((rawExecution xs).init q) =
      (rawExecution xs).init q := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      cases j <;> simp
    · simp [hj]
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      cases j <;> simp
    · simp [hj]
  · rfl

/-- Output redirection preserves a standard input run. -/
theorem run_eq (e : (κ ⊕ Unit) ↪ τ) (M : TM Id κ Γ Q) (xs : List Γ) (n : ℕ) :
    (compilerAlong e M).run (Cfg τ Γ Q xs.toArray) xs n =
      cfgAlong e (M.run _ xs n)
        ((compilerAlong e M).initInput (Config := Cfg τ Γ Q xs.toArray) xs) := by
  simpa only [Controller.run, Controller.initInput, cfg_init,
    show (compilerAlong e M).q₀ = M.q₀ from rfl] using
    runFrom_cfgAlong e M ((rawExecution xs).init M.q₀)
      ((rawExecution xs).init M.q₀) n

end Layout

end Complexity.TM.RedirectOutput
