/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Call
public import Complexity.Models.TuringMachine.Program.Word.Basic
public import Complexity.Models.TuringMachine.RedirectInput
public import Complexity.Models.TuringMachine.RedirectOutput
public import Mathlib.Logic.Equiv.Sum

/-! # Calling a binary machine through two work buffers

The source bank is the left summand. The right summand contains a `false` input buffer
and a `true` output buffer. The caller's external input head and output are preserved.
-/

@[expose] public section

namespace Complexity.TM.Program.BufferedCall

open Std.WP

variable {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Type}
    {xs ys : List Bool} {zs : Array (Option Bool)}

/-- Pack the two successive stream buffers into the canonical `Bool` coordinates. -/
def bufferEmbedding : ((κ ⊕ Unit) ⊕ Unit) ↪ (κ ⊕ Bool) :=
  ((Equiv.sumAssoc κ Unit Unit).trans
    (Equiv.sumCongr (Equiv.refl κ) Equiv.boolEquivPUnitSumPUnit.symm)).toEmbedding

/-- Redirect both streams without adding transitions. -/
def compiler (M : TM Id κ (Option Bool) Q) :
    TM Id (κ ⊕ Bool) (Option Bool) (Q × Bool) :=
  RedirectOutput.compilerAlong bufferEmbedding
    (RedirectInput.compilerAlong (.refl _) M)

/-- Represent a source configuration with independent external streams. -/
def cfg (xs : List Bool) (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    Cfg (κ ⊕ Bool) (Option Bool) (Q × Bool) zs :=
  RedirectOutput.cfgAlong bufferEmbedding
    (RedirectInput.cfgAlong (.refl _) xs.toArray
      (d.restrictWorkAlong (Function.Embedding.inl.trans bufferEmbedding)) c l) d

@[simp] theorem state_cfg (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).state = (c.state, l) := rfl

@[simp] theorem inputPos_cfg (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).inputPos = d.inputPos := rfl

@[simp] theorem output_cfg (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).output = d.output := rfl

@[simp] theorem workTapes_cfg_work (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) (j : κ) :
    (cfg xs d c l).workTapes (Sum.inl j) = c.workTapes j := by
  change (cfg xs d c l).workTapes (bufferEmbedding (.inl (.inl j))) = _
  simp only [cfg, RedirectOutput.cfgAlong_workTapes, Function.Embedding.replace_apply,
    Sum.elim_inl, RedirectInput.cfgAlong]
  exact (Function.Embedding.refl (κ ⊕ Unit)).replace_apply _ _ (.inl j)

@[simp] theorem workPos_cfg_work (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) (j : κ) :
    (cfg xs d c l).workPos (Sum.inl j) = c.workPos j := by
  change (cfg xs d c l).workPos (bufferEmbedding (.inl (.inl j))) = _
  simp only [cfg, RedirectOutput.cfgAlong_workPos, Function.Embedding.replace_apply,
    Sum.elim_inl, RedirectInput.cfgAlong]
  exact (Function.Embedding.refl (κ ⊕ Unit)).replace_apply _ _ (.inl j)

@[simp] theorem workTapes_cfg_input (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).workTapes (Sum.inr false) = Word.tape xs := by
  change (cfg xs d c l).workTapes (bufferEmbedding (.inl (.inr ()))) = _
  simp only [cfg, RedirectOutput.cfgAlong_workTapes, Function.Embedding.replace_apply,
    Sum.elim_inl, RedirectInput.cfgAlong]
  exact (Function.Embedding.refl (κ ⊕ Unit)).replace_apply _ _ (.inr ())

@[simp] theorem workPos_cfg_input (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).workPos (Sum.inr false) = RedirectInput.position c.inputPos := by
  change (cfg xs d c l).workPos (bufferEmbedding (.inl (.inr ()))) = _
  simp only [cfg, RedirectOutput.cfgAlong_workPos, Function.Embedding.replace_apply,
    Sum.elim_inl, RedirectInput.cfgAlong]
  exact (Function.Embedding.refl (κ ⊕ Unit)).replace_apply _ _ (.inr ())

@[simp] theorem workTapes_cfg_output (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).workTapes (Sum.inr true) = IntMemory.ofArray c.output := by
  change (cfg xs d c l).workTapes (bufferEmbedding (.inr ())) = _
  simp [cfg, RedirectInput.cfgAlong]

@[simp] theorem workPos_cfg_output (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool) :
    (cfg xs d c l).workPos (Sum.inr true) = c.output.size := by
  change (cfg xs d c l).workPos (bufferEmbedding (.inr ())) = _
  simp [cfg, RedirectInput.cfgAlong]

/-- The redirected run follows the source run, retaining a finite boundary flag. -/
theorem runFrom_cfg (M : TM Id κ (Option Bool) Q)
    (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (c : Cfg κ (Option Bool) Q (xs.map some).toArray) (l : Bool)
    (hl : RedirectInput.Boundary c.inputPos l) (n : ℕ) :
    ∃ l', RedirectInput.Boundary (M.runFrom c n).inputPos l' ∧
      (compiler M).runFrom (cfg xs d c l) n = cfg xs d (M.runFrom c n) l' := by
  obtain ⟨l', hl', h⟩ := RedirectInput.runFrom_cfgAlong (.refl _) M xs.toArray
    (d.restrictWorkAlong (Function.Embedding.inl.trans bufferEmbedding)) c l hl n
  refine ⟨l', hl', ?_⟩
  unfold compiler cfg
  rw [RedirectOutput.runFrom_cfgAlong bufferEmbedding, h]
  rfl

omit [Fintype κ] [DecidableEq κ] in
/-- The source bank and two named buffers determine every target work coordinate. -/
private theorem work_ext {α : Type*} {f g : (κ ⊕ Bool) → α}
    (hw : ∀ j : κ, f (Sum.inl j) = g (Sum.inl j))
    (hi : f (Sum.inr false) = g (Sum.inr false))
    (ho : f (Sum.inr true) = g (Sum.inr true)) : f = g := by
  funext j
  rcases j with j | b
  · exact hw j
  · cases b
    · exact hi
    · exact ho

/-- Recognize a caller configuration containing fresh source tapes and prepared buffers. -/
theorem cfg_init_eq (M : TM Id κ (Option Bool) Q)
    (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs)
    (hw : ∀ j : κ, d.workTapes (Sum.inl j) = ∅)
    (hp : ∀ j : κ, d.workPos (Sum.inl j) = 0)
    (hi : d.workTapes (Sum.inr false) = Word.tape xs)
    (hip : d.workPos (Sum.inr false) = 0)
    (ho : d.workTapes (Sum.inr true) = ∅)
    (hop : d.workPos (Sum.inr true) = 0) :
    (cfg (Q := Q) xs d (M.initInput (xs.map some)) false).mapState
      (fun _ ↦ ()) = d := by
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · apply work_ext
    · intro j
      exact (workTapes_cfg_work (Q := Q) d (M.initInput (xs.map some))
        false j).trans (hw j).symm
    · simpa using hi.symm
    · simpa [initInput_raw] using ho.symm
  · apply work_ext
    · intro j
      exact (workPos_cfg_work (Q := Q) d (M.initInput (xs.map some))
        false j).trans (hp j).symm
    · simpa [initInput_raw, RedirectInput.position] using hip.symm
    · simpa [initInput_raw] using hop.symm
  · rfl

variable [FinEnum Q]

/-- Invoke an existing machine through the two prepared work buffers. -/
def program (M : TM Id κ (Option Bool) Q) : TM.Program (κ ⊕ Bool) (Option Bool) Unit := do
  let _ ← call (compiler M)
  pure ()

/-- The call has at most the source running time and preserves the caller's external streams. -/
@[spec] theorem spec (M : TM Id κ (Option Bool) Q)
    (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs) (t q : ℕ)
    (h : M.Halted (M.run (Cfg κ (Option Bool) Q (xs.map some).toArray) (xs.map some) t)) :
    Triple ((program M).verify (cfgSemantics zs))
      (fun u b ↦ u = (cfg (Q := Q) xs d (M.initInput (xs.map some)) false).mapState
        (fun _ ↦ ()) ∧ t + q ≤ b)
      (fun _ u b ↦ ∃ l, u =
        (cfg (Q := Q) xs d (M.run _ (xs.map some) t) l).mapState
          (fun _ ↦ ()) ∧ q ≤ b) () := by
  obtain ⟨l, _, hr⟩ := runFrom_cfg (xs := xs) M d (M.initInput (xs.map some)) false
    (by intro _; rfl) t
  have hh : (compiler M).Halted ((compiler M).runFrom
      (cfg (Q := Q) xs d (M.initInput (xs.map some)) false) t) := by
    rw [hr]
    exact h
  have hc := cfg_spec_call (compiler M)
    (cfg (Q := Q) xs d (M.initInput (xs.map some)) false) t q rfl hh
  constructor
  intro u b hu
  obtain ⟨n, a, v, hn, he, ha, hv, hb⟩ := hc.le_wp u b hu
  refine ⟨n + 0, (), v, by omega, ?_, l, ?_, hb⟩
  · exact Program.Exec.bind he (Program.Exec.pure _ _ _)
  · simpa only [Controller.run, hr] using hv

/-- A field-oriented interface for prepared buffers. Source work tapes may contain arbitrary
results afterwards; the input buffer and both external streams are preserved. -/
@[spec] theorem spec_ready (M : TM Id κ (Option Bool) Q)
    (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs) (t q : ℕ)
    (h : M.Halted (M.run (Cfg κ (Option Bool) Q (xs.map some).toArray) (xs.map some) t))
    (hy : (M.run (Cfg κ (Option Bool) Q (xs.map some).toArray) (xs.map some) t).output =
      (ys.map some).toArray)
    (hw : ∀ j : κ, d.workTapes (Sum.inl j) = ∅)
    (hp : ∀ j : κ, d.workPos (Sum.inl j) = 0)
    (hi : d.workTapes (Sum.inr false) = Word.tape xs)
    (hip : d.workPos (Sum.inr false) = 0)
    (ho : d.workTapes (Sum.inr true) = ∅)
    (hop : d.workPos (Sum.inr true) = 0) :
    Triple ((program M).verify (cfgSemantics zs))
      (fun u b ↦ u = d ∧ t + q ≤ b)
      (fun _ u b ↦ u.workTapes (Sum.inr true) = Word.tape ys ∧
        u.workPos (Sum.inr true) = (ys.length : ℤ) ∧
        u.workTapes (Sum.inr false) = Word.tape xs ∧
        u.inputPos = d.inputPos ∧ u.output = d.output ∧ q ≤ b) () := by
  have he := cfg_init_eq M d hw hp hi hip ho hop
  constructor
  intro u b hu
  obtain ⟨n, a, v, hn, hx, l, hv, hb⟩ :=
    (spec M d t q h).le_wp u b ⟨hu.1.trans he.symm, hu.2⟩
  refine ⟨n, a, v, hn, hx, ?_⟩
  subst v
  simp only [Cfg.mapState_workTapes, Cfg.mapState_workPos, Cfg.mapState_inputPos,
    Cfg.mapState_output, workTapes_cfg_output, workPos_cfg_output,
    workTapes_cfg_input, inputPos_cfg, output_cfg, hy, List.size_toArray, List.length_map]
  simpa only [Word.tape, IntMemory.ofList, true_and, and_true] using hb

/-- Invoke a standard list computation through prepared buffers. The source time bound
pays for the call; the source space bound is not a bound on the caller's combined storage. -/
@[spec] theorem spec_of_computes (M : TM Id κ (Option Bool) Q)
    {xs ys : List Bool} {t s : ℕ}
    (d : Cfg (κ ⊕ Bool) (Option Bool) Unit zs) (q : ℕ)
    (h : M.ComputesInTimeAndSpace (xs.map some) (ys.map some) t s)
    (hw : ∀ j : κ, d.workTapes (Sum.inl j) = ∅)
    (hp : ∀ j : κ, d.workPos (Sum.inl j) = 0)
    (hi : d.workTapes (Sum.inr false) = Word.tape xs)
    (hip : d.workPos (Sum.inr false) = 0)
    (ho : d.workTapes (Sum.inr true) = ∅)
    (hop : d.workPos (Sum.inr true) = 0) :
    Triple ((program M).verify (cfgSemantics zs))
      (fun u b ↦ u = d ∧ t + q ≤ b)
      (fun _ u b ↦ u.workTapes (Sum.inr true) = Word.tape ys ∧
        u.workPos (Sum.inr true) = (ys.length : ℤ) ∧
        u.workTapes (Sum.inr false) = Word.tape xs ∧
        u.inputPos = d.inputPos ∧ u.output = d.output ∧ q ≤ b) () := by
  exact spec_ready M d t q h.1 h.2.1 hw hp hi hip ho hop

end Complexity.TM.Program.BufferedCall
