/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Data.Embedding
public import Complexity.Control.Transition.Simulation
public import Complexity.Models.TuringMachine.Tapes
public import Mathlib.Data.Fintype.Sum

/-!
# Reading a binary input from an additional work tape

Data cells contain `some` bits. The two neighbouring blank cells represent the clamped
input boundaries. A finite flag distinguishes those boundaries without recording the
input length in the controller.
-/

@[expose] public section

namespace Complexity.TM.RedirectInput

/-- A binary input contains data bits only, with `none` reserved for its boundaries. -/
def input (xs : Array Bool) : Array (Option Bool) := (xs.toList.map some).toArray

@[simp] theorem size_input (xs : Array Bool) : (input xs).size = xs.size := by simp [input]

/-- Store the original input at addresses `0` through `size - 1`. -/
def buffer (xs : Array Bool) : IntMemory (Option Bool) := IntMemory.ofArray (input xs)

/-- Address `-1` is the left boundary; address `size` is the right boundary. -/
def position {n : ℕ} (p : Fin (n + 2)) : ℤ := (p.val : ℤ) - 1

/-- The flag matters only when the head is at one of the two blank boundaries. -/
def Boundary {n : ℕ} (p : Fin (n + 2)) (l : Bool) : Prop :=
  p.val = 0 ∨ p.val = n + 1 → l = decide (p.val = 0)

/-- Clamp only outward moves made while a blank boundary is scanned. -/
def movement (l : Bool) (a : Option Bool) (d : SignType) : SignType :=
  if a = none ∧ (if l then d = -1 else d = 1) then 0 else d

/-- Remember which boundary a move could have reached. -/
def nextLeft (l : Bool) : SignType → Bool
  | .neg => true
  | .zero => l
  | .pos => false

theorem boundary_next {n : ℕ} (p : Fin (n + 2)) (l : Bool) (d : SignType)
    (hl : Boundary p l) : Boundary (moveInputPos p d) (nextLeft l d) := by
  intro h
  have := p.isLt
  cases d with
  | neg =>
    have hp : p.val - 1 = 0 := by
      change p.val - 1 = 0 ∨ p.val - 1 = n + 1 at h
      omega
    simp [nextLeft, moveInputPos, hp]
  | zero => exact hl h
  | pos => simp [nextLeft, moveInputPos]

/-- Translating a clamped input move is exactly one legal work-head move. -/
theorem position_move {n : ℕ} (p : Fin (n + 2)) (l : Bool) (a : Option Bool)
    (d : SignType) (ha : a = none ↔ p.val = 0 ∨ p.val = n + 1) (hl : Boundary p l) :
    position p + (movement l a d).cast = position (moveInputPos p d) := by
  have := p.isLt
  by_cases h₀ : p.val = 0
  · have he := ha.mpr (Or.inl h₀)
    have hf : l = true := by simpa [h₀] using hl (Or.inl h₀)
    cases d <;> simp [movement, he, hf, position, moveInputPos, h₀, SignType.cast]
  · by_cases h₁ : p.val = n + 1
    · have he := ha.mpr (Or.inr h₁)
      have hf : l = false := by simpa [h₀] using hl (Or.inr h₁)
      cases d <;> simp [movement, he, hf, position, moveInputPos, h₁, SignType.cast]
      omega
    · have he : a ≠ none := by simpa [h₀, h₁] using ha
      cases d <;> simp [movement, he, position, moveInputPos, SignType.cast] <;> omega

private theorem buffer_read (xs : Array Bool) (p : ℕ) :
    (buffer xs)[(p : ℤ) - 1] = match p with | 0 => none | n + 1 => xs[n]? := by
  cases p with
  | zero => rfl
  | succ n =>
    have h : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [h]
    simp only [buffer, IntMemory.getElem_ofArray_natCast, input,
      ← List.map_toArray, Array.toArray_toList, Array.getElem?_map]
    cases xs[n]? <;> rfl

/-- The work buffer supplies exactly the source machine's read-only input observation. -/
theorem buffer_inputSymbol {κ : Type*} {Q : Type*} (xs : Array Bool)
    (c : Cfg κ (Option Bool) Q (input xs)) :
    (buffer xs)[position c.inputPos] = c.inputSymbol := by
  rw [position, buffer_read]
  unfold Cfg.inputSymbol
  cases h : c.inputPos.val with
  | zero => rfl
  | succ n =>
    simp only [input, ← List.map_toArray, Array.toArray_toList, Array.getElem?_map]
    cases xs[n]? <;> rfl

/-- Data bits cannot be confused with either blank boundary. -/
theorem inputSymbol_eq_none_iff {κ : Type*} {Q : Type*} (xs : Array Bool)
    (c : Cfg κ (Option Bool) Q (input xs)) :
    c.inputSymbol = none ↔ c.inputPos.val = 0 ∨ c.inputPos.val = xs.size + 1 := by
  rw [← buffer_inputSymbol, position, buffer_read]
  have ht : c.inputPos.val < xs.size + 2 := by simpa using c.inputPos.isLt
  cases h : c.inputPos.val with
  | zero => simp
  | succ n =>
    simp only [Array.getElem?_eq_none_iff, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, false_or]
    omega

variable {Q Δ : Type*}

section Layout

variable {κ τ : Type*} [Fintype κ] [DecidableEq τ]

/-- Route the source work bank and its input buffer through one embedding. -/
@[simps]
def actionAlong (e : (κ ⊕ Unit) ↪ τ) (l : Bool) (r : Option Bool)
    (a : Action κ (Option Bool) Q) : Action τ (Option Bool) (Q × Bool) where
  inputMove := 0
  work := e.replace (Sum.elim a.work (fun _ ↦ (none, movement l r a.inputMove)))
    (fun _ ↦ (none, 0))
  output := a.output
  state := (a.state, nextLeft l a.inputMove)

/-- Compile input redirection; injectivity separates the buffer from source work tapes. -/
@[simps]
def compilerAlong (e : (κ ⊕ Unit) ↪ τ) (M : TM Id κ (Option Bool) Q) :
    TM Id τ (Option Bool) (Q × Bool) where
  q₀ := (M.q₀, false)
  halt q := M.halt q.1
  transition := fun q (_, v) ↦ pure <|
    actionAlong e q.2 (v (e (.inr ())))
      ((M.transition q.1 (v (e (.inr ())), v ∘ (Function.Embedding.inl.trans e))).run)

/-- Install the source bank and input buffer without changing the caller's external input. -/
@[simps]
def cfgAlong (e : (κ ⊕ Unit) ↪ τ) (xs : Array Bool) {ys : Array (Option Bool)}
    (s : Cfg τ (Option Bool) Δ ys) (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool) :
    Cfg τ (Option Bool) (Q × Bool) ys where
  state := (c.state, l)
  inputPos := s.inputPos
  workTapes := e.replace (Sum.elim c.workTapes (fun _ ↦ buffer xs)) s.workTapes
  workPos := e.replace (Sum.elim c.workPos (fun _ ↦ position c.inputPos)) s.workPos
  output := c.output

/-- Input redirection preserves the source work bank in one target action. -/
theorem action_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (xs : Array Bool) {ys : Array (Option Bool)} (s : Cfg τ (Option Bool) Δ ys)
    (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool)
    (a : Action κ (Option Bool) Q) (hl : Boundary c.inputPos l) :
    apply (actionAlong e l c.inputSymbol a)
      (cfgAlong e xs s c l) =
      cfgAlong e xs s (apply a c) (nextLeft l a.inputMove) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      rcases j with j | ⟨⟩ <;> simp
    · simp [hj]
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hj
      rcases j with j | ⟨⟩
      · simp
      · simpa using
          position_move c.inputPos l c.inputSymbol a.inputMove
            (by simpa using inputSymbol_eq_none_iff xs c) hl
    · simp [hj]
  · rfl

/-- The embedded input buffer supplies the source input observation. -/
theorem workSymbols_cfgAlong_input (e : (κ ⊕ Unit) ↪ τ)
    (xs : Array Bool) {ys : Array (Option Bool)}
    (s : Cfg τ (Option Bool) Δ ys) (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool) :
    (cfgAlong e xs s c l).workSymbols (e (.inr ())) = c.inputSymbol := by
  simp [Cfg.workSymbols, buffer_inputSymbol]

/-- Source work observations are read through the embedding. -/
theorem workSymbols_cfgAlong_restrict (e : (κ ⊕ Unit) ↪ τ)
    (xs : Array Bool) {ys : Array (Option Bool)} (s : Cfg τ (Option Bool) Δ ys)
    (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool) :
    (cfgAlong e xs s c l).workSymbols ∘ (Function.Embedding.inl.trans e) =
      c.workSymbols := by
  funext j
  simp [Function.comp_def, Cfg.workSymbols]

/-- Input redirection simulates one source step with a finite boundary flag. -/
theorem step_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ (Option Bool) Q) (xs : Array Bool)
    {ys : Array (Option Bool)} (s : Cfg τ (Option Bool) Δ ys)
    (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool) (hl : Boundary c.inputPos l) :
    ∃ l', Boundary (M.step c).inputPos l' ∧
      (compilerAlong e M).step (cfgAlong e xs s c l) = cfgAlong e xs s (M.step c) l' := by
  by_cases hh : M.halt c.state = true
  · have hc : M.Halted c := hh
    have ht : (compilerAlong e M).Halted (cfgAlong e xs s c l) := hh
    refine ⟨l, ?_, ?_⟩
    · simpa only [M.step_of_halted c hc, Pure.pure] using hl
    · rw [M.step_of_halted c hc, (compilerAlong e M).step_of_halted _ ht]
  · have hf : M.halt c.state = false := Bool.eq_false_iff.mpr hh
    let a := (M.transition c.state (c.inputSymbol, c.workSymbols)).run
    have hm := M.step_eq c
    simp only [hf, Bool.false_eq_true, ite_false] at hm
    refine ⟨nextLeft l a.inputMove, ?_, ?_⟩
    · rw [hm]
      exact boundary_next c.inputPos l a.inputMove hl
    · rw [hm]
      simp only [TM.step_eq]
      change (if M.halt c.state then _ else _) = _
      simp only [hf, Bool.false_eq_true, ite_false]
      change apply
        (actionAlong e l ((cfgAlong e xs s c l).workSymbols (e (.inr ())))
        ((M.transition c.state ((cfgAlong e xs s c l).workSymbols (e (.inr ())),
          (cfgAlong e xs s c l).workSymbols ∘ (Function.Embedding.inl.trans e))).run)) _ = _
      rw [workSymbols_cfgAlong_input, workSymbols_cfgAlong_restrict]
      exact action_cfgAlong e xs s c l a hl

/-- The embedding preserves every finite source run and its boundary invariant. -/
theorem runFrom_cfgAlong (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ (Option Bool) Q) (xs : Array Bool)
    {ys : Array (Option Bool)} (s : Cfg τ (Option Bool) Δ ys)
    (c : Cfg κ (Option Bool) Q (input xs)) (l : Bool) (hl : Boundary c.inputPos l) (n : ℕ) :
    ∃ l', Boundary (M.runFrom c n).inputPos l' ∧
      (compilerAlong e M).runFrom (cfgAlong e xs s c l) n =
        cfgAlong e xs s (M.runFrom c n) l' := by
  apply Transition.rel_runN
    (R := fun (c : Cfg κ (Option Bool) Q (input xs)) d ↦ ∃ l,
      Boundary c.inputPos l ∧ d = cfgAlong e xs s c l) (f := M.step) (g := (compilerAlong e M).step)
    (fun c d h ↦ ?_) ⟨l, hl, rfl⟩ n
  rcases h with ⟨l, hl, rfl⟩
  exact step_cfgAlong e M xs s c l hl

/-- The caller may begin with the input buffer at head zero and the source's initial state. -/
theorem runFrom_init (e : (κ ⊕ Unit) ↪ τ)
    (M : TM Id κ (Option Bool) Q) (xs : List Bool)
    {ys : Array (Option Bool)} (s : Cfg τ (Option Bool) Δ ys) (n : ℕ) :
    ∃ l', Boundary
        (M.run (Cfg κ (Option Bool) Q (xs.map some).toArray)
          (xs.map some) n).inputPos l' ∧
      (compilerAlong e M).runFrom
        (cfgAlong e xs.toArray s
          (M.initInput (Config := Cfg κ (Option Bool) Q (xs.map some).toArray)
            (xs.map some)) false) n =
        cfgAlong e xs.toArray s
          (M.run (Cfg κ (Option Bool) Q (xs.map some).toArray)
            (xs.map some) n) l' :=
  runFrom_cfgAlong e M xs.toArray s
    (M.initInput (Config := Cfg κ (Option Bool) Q (xs.map some).toArray) (xs.map some))
    false (by intro _; rfl) n

end Layout

end Complexity.TM.RedirectInput
