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
public import Mathlib.Data.Int.Interval

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

/-- The original work tapes visit exactly the same positions after embedding. -/
theorem visited_embed (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ) (j : κ) :
    (compilerAlong e M).visited (cfgAlong e c d) n (e (.inl j)) =
      M.visited c n j := by
  simp only [TM.visited, runFrom_cfgAlong]
  simp

/-- The output buffer stays between its starting and ending output lengths. -/
theorem visited_self_subset (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ) :
    (compilerAlong e M).visited (cfgAlong e c d) n (e (.inr ())) ⊆
      Finset.Icc (c.output.size : ℤ) (M.runFrom c n).output.size := by
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  rw [runFrom_cfgAlong]
  simp only [cfgAlong_workPos, Function.Embedding.replace_apply, Sum.elim_inr, Finset.mem_Icc]
  exact ⟨by exact_mod_cast M.output_size_le_runFrom c u,
    by exact_mod_cast M.output_size_runFrom_mono c (Finset.mem_range_succ_iff.mp hu)⟩

/-- Heads outside the embedding never move. -/
theorem visited_extra (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (d : Cfg τ Γ Δ xs) (n : ℕ)
    (j : τ) (hj : j ∉ Set.range e) :
    (compilerAlong e M).visited (cfgAlong e c d) n j = {d.workPos j} := by
  simp only [TM.visited, runFrom_cfgAlong]
  simp [hj, Finset.image_const]

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
