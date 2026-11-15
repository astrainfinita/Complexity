/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Expression
public import Complexity.Models.TreeMachine.Language.Bounds

/-! # Compiling structured tree programs

Source variables have fixed slots. Expression temporaries are reused across statements and
loop iterations; the number of registers depends only on the program. Source runs
transport their value, exact unit time and bounds on every intermediate register tree.
-/

@[expose] public section

namespace Complexity.TreeProgram

open Controller (History)

variable {ν : Type} {k : ℕ}

/-- Read the result's root, using existing registers directly for atoms. -/
def Expr.test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program k Bool := do
  let i ← e.compile v z b hb
  TreeMachine.Program.root i

theorem Expr.exec_test_history (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hz : s.last.regs z = .nil) :
    ∃ t, (e.test v z b hb).Exec TreeMachine.Program.historySemantics s (e.steps + 1)
      (e.eval (s.last.regs ∘ v)).root t ∧ t.last.regs ∘ v = s.last.regs ∘ v ∧
      t.last.regs z = .nil ∧ ∀ j, t.configSup (fun c ↦ (c.regs j).size) ≤
        s.configSup (fun c ↦ (c.regs j).size) ⊔ e.maxSize (s.last.regs ∘ v) := by
  obtain ⟨t, i, he, hval, _, hf, hpeak⟩ := e.exec_compile_history v z b hb hv hzv s hz
  refine ⟨t.snoc .nop, ?_, ?_, ?_, ?_⟩
  · have ht := Program.Exec.perform TreeMachine.Program.historySemantics
      (TreeMachine.Program.Op.root i) t
    change (TreeMachine.Program.root i).Exec _ _ 1 (t.last.regs i).root _ at ht
    rw [hval] at ht
    exact he.bind ht
  · simpa only [History.last_snoc, TreeMachine.Action.apply_nop, Function.comp_def]
      using funext (fun x ↦ hf (v x) (hv x))
  · simpa using (hf z hzv).trans hz
  · intro j
    rw [TreeMachine.configSup_snoc_nop t (fun c ↦ (c.regs j).size)]
    exact hpeak j

theorem Expr.exec_test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (c : TreeMachine.Cfg k) (hz : c.regs z = .nil) :
    ∃ σ, (e.test v z b hb).Exec TreeMachine.Program.semantics c (e.steps + 1)
      (e.eval (c.regs ∘ v)).root σ ∧ σ.regs ∘ v = c.regs ∘ v ∧ σ.regs z = .nil := by
  obtain ⟨t, ht, hf, hz, _⟩ := e.exec_test_history v z b hb hv hzv (History.nil c) hz
  exact ⟨t.last, ht.map (fun h ↦ h.last) (fun _ ↦ rfl) (by intro a h; simp), hf, hz⟩

/-- Scratch space shared by all executions of a statement. -/
def Cmd.slots : Cmd ν → ℕ
  | .skip => 0
  | .assign _ e => e.slots
  | .seq p q => max p.slots q.slots
  | .branch e p q => max e.slots (max p.slots q.slots)
  | .while e p => max e.slots p.slots

/-- Compile assignments and root tests, allocating expression temporaries above `b`. -/
def Cmd.compile (p : Cmd ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + p.slots ≤ k) : TreeMachine.Program k Unit :=
  match p with
  | .skip => pure ()
  | .assign x e => e.assign (v x) v z b hb
  | .seq p q => do
      p.compile v z b (by simp only [slots] at hb; omega)
      q.compile v z b (by simp only [slots] at hb; omega)
  | .branch e p q => do
      let c ← e.test v z b (by simp only [slots] at hb; omega)
      if c then p.compile v z b (by simp only [slots] at hb; omega)
      else q.compile v z b (by simp only [slots] at hb; omega)
  | .while e p => TreeMachine.Program.repeatUntil do
      let c ← e.test v z b (by simp only [slots] at hb; omega)
      if c then do
        p.compile v z b (by simp only [slots] at hb; omega)
        pure false
      else pure true

/-- Source runs transport their value, exact unit time and independent peak-size bound. -/
theorem Cmd.Run.compile_history [DecidableEq ν] {p : Cmd ν} {s t : ν → Tree} {n a : ℕ}
    (h : p.Run s n t a) (v : ν → Fin k) (hi : Function.Injective v) (z : Fin k) (b : ℕ)
    (hb : b + p.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (hvz : ∀ x, v x ≠ z)
    (ρ : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hρ : ρ.last.regs ∘ v = s) (hz : ρ.last.regs z = .nil) :
    ∃ σ, (p.compile v z b hb).Exec TreeMachine.Program.historySemantics ρ n () σ ∧
      σ.last.regs ∘ v = t ∧ σ.last.regs z = .nil ∧ ∀ j,
      σ.configSup (fun c ↦ (c.regs j).size) ≤
        ρ.configSup (fun c ↦ (c.regs j).size) ⊔ (a + 2) := by
  induction h generalizing ρ with
  | skip s => exact ⟨ρ, Program.Exec.pure _ _ _, hρ, hz, fun _ ↦ le_sup_left⟩
  | assign x e s =>
    obtain ⟨σ, he, hf, hpeak⟩ := e.exec_assign_history (v x) v z b hb hv hzv ρ hz
    refine ⟨σ, he, ?_, ?_, ?_⟩
    · rw [← hρ, ← Function.update_comp_eq_of_injective ρ.last.regs hi]
      exact funext fun y ↦ hf (v y) (hv y)
    · simpa [Ne.symm (hvz x), hz] using hf z hzv
    · simpa only [hρ] using hpeak
  | seq hp hq ihp ihq =>
    obtain ⟨σ, hp', hσ, hzσ, hs⟩ := ihp (by simp only [Cmd.slots] at hb; omega) ρ hρ hz
    obtain ⟨τ, hq', hτ, hzτ, ht⟩ := ihq (by simp only [Cmd.slots] at hb; omega) σ hσ hzσ
    exact ⟨τ, hp'.bind hq', hτ, hzτ, fun j ↦ by have := hs j; have := ht j; omega⟩
  | @branch_true e p q s t n a he hp ih | @branch_false e p q s t n a he hp ih =>
    obtain ⟨σ, ht, hσ, hzσ, hs⟩ := Expr.exec_test_history e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ hz
    obtain ⟨τ, hp', hτ, hzτ, hp⟩ := ih (by simp only [Cmd.slots] at hb; omega)
      σ (hσ.trans hρ) hzσ
    refine ⟨τ, ht.bind ?_, hτ, hzτ, ?_⟩
    · simpa only [hρ, he, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] using hp'
    · intro j
      have := hs j
      have := hp j
      simp only [hρ] at *
      omega
  | @while_false e p s he =>
    let ρ' := ρ.snoc .nop
    obtain ⟨σ, ht, hσ, hzσ, hs⟩ := Expr.exec_test_history e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ' (by simpa [ρ'] using hz)
    refine ⟨σ, ?_, ?_, hzσ, ?_⟩
    · rw [show e.steps + 2 = e.steps + 1 + 0 + 1 by omega]
      apply Program.Exec.repeatUntilWith_done TreeMachine.Action.nop
      apply ht.bind (n := 0)
      simp only [ρ', History.last_snoc, TreeMachine.Action.apply_nop, hρ, he,
        Bool.false_eq_true, ite_false]
      exact Program.Exec.pure TreeMachine.Program.historySemantics true σ
    · simpa [ρ', hρ] using hσ
    · intro j
      have := hs j
      simp only [ρ', TreeMachine.configSup_snoc_nop ρ (fun c ↦ (c.regs j).size),
        History.last_snoc,
        TreeMachine.Action.apply_nop, hρ] at this
      omega
  | @while_true e p s t u n m a c he hp hr ihp ihr =>
    let ρ' := ρ.snoc .nop
    obtain ⟨σ, ht, hσ, hzσ, hs⟩ := Expr.exec_test_history e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ' (by simpa [ρ'] using hz)
    obtain ⟨τ, hp', hτ, hzτ, hp⟩ := ihp (by simp only [Cmd.slots] at hb; omega)
      σ (by simpa [ρ', hρ] using hσ) hzσ
    obtain ⟨υ, hr', hυ, hzυ, hr⟩ := ihr hb τ hτ hzτ
    refine ⟨υ, ?_, hυ, hzυ, ?_⟩
    · rw [show e.steps + 2 + n + m = e.steps + 1 + (n + 0) + m + 1 by omega]
      apply Program.Exec.repeatUntilWith_next TreeMachine.Action.nop _ (ht.bind ?_) hr'
      simp only [ρ', History.last_snoc, TreeMachine.Action.apply_nop, hρ, he, ite_true]
      exact hp'.bind (Program.Exec.pure TreeMachine.Program.historySemantics false τ)
    · intro j
      have := hs j
      have := hp j
      have := hr j
      simp only [ρ', TreeMachine.configSup_snoc_nop ρ (fun c ↦ (c.regs j).size),
        History.last_snoc,
        TreeMachine.Action.apply_nop, hρ] at *
      omega

/-- Functional correctness is the projection of the same resource-preserving compilation. -/
theorem Cmd.Exec.compile [DecidableEq ν] {p : Cmd ν} {s t : ν → Tree}
    (h : p.Exec s t) (v : ν → Fin k) (hi : Function.Injective v) (z : Fin k) (b : ℕ)
    (hb : b + p.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (hvz : ∀ x, v x ≠ z) (c : TreeMachine.Cfg k) (hc : c.regs ∘ v = s) (hz : c.regs z = .nil) :
    ∃ n σ, (p.compile v z b hb).Exec TreeMachine.Program.semantics c n () σ ∧
      σ.regs ∘ v = t ∧ σ.regs z = .nil := by
  obtain ⟨n, a, h⟩ := h
  obtain ⟨σ, hr, ht, hz, _⟩ := h.compile_history v hi z b hb hv hzv hvz
    (History.nil c) hc hz
  exact ⟨n, σ.last, hr.map (fun h ↦ h.last) (fun _ ↦ rfl) (by intro a h; simp), ht, hz⟩

namespace Procedure

variable [FinEnum ν]

/-- One slot per source variable, standard input/output, an empty tree, and shared scratch. -/
def registers (p : Procedure ν) : ℕ :=
  FinEnum.card ν + 2 + max p.body.slots p.result.slots

instance (p : Procedure ν) : NeZero p.registers := ⟨by simp only [registers]; omega⟩

/-- The slot assigned to a source variable. -/
def register (p : Procedure ν) (x : ν) : Fin p.registers :=
  ⟨(FinEnum.equiv x).val + 1, by
    have := (FinEnum.equiv x).isLt
    simp only [registers]
    omega⟩

/-- The read-only empty-tree register used by the compiler. -/
def empty (p : Procedure ν) : Fin p.registers :=
  ⟨FinEnum.card ν + 1, by simp only [registers]; omega⟩

private theorem register_injective (p : Procedure ν) : Function.Injective p.register := by
  intro x y h
  exact FinEnum.equiv.injective (Fin.ext (Nat.add_right_cancel (congrArg Fin.val h)))

private theorem register_lt (p : Procedure ν) (x : ν) :
    (p.register x).val < FinEnum.card ν + 2 := by
  simp [register]
  omega

private theorem register_ne_empty (p : Procedure ν) (x : ν) : p.register x ≠ p.empty := by
  simp [register, empty, Fin.ext_iff, (FinEnum.equiv x).isLt.ne]

/-- The generated register program. User specifications should use `Procedure.Exec`. -/
def code (p : Procedure ν) : TreeMachine.Program p.registers Unit := do
  TreeMachine.Program.copy p.empty (p.register p.input) 0
  p.body.compile p.register p.empty (FinEnum.card ν + 2) (by simp [registers])
  p.result.assign 0 p.register p.empty (FinEnum.card ν + 2) (by simp [registers])

/-- A finite tree machine with automatically chosen registers and control states. -/
def compile (p : Procedure ν) : TreeMachine Id p.registers (p.code.State ⊕ p.code.Exit) :=
  p.code.compile

/-- A source contract yields machine time and independent space. The static register count
covers retained locals; two extra tree nodes cover the copy macro's temporary pair. -/
theorem Bounded.compile {p : Procedure ν} {x y : Tree} {time space : ℕ}
    (h : p.Bounded x y time space) :
    p.compile.ComputesInUnitTimeAndSpace x y time (p.registers * (space + 2)) := by
  obtain ⟨n, s, a, hr, hy, ht, hx, ha, hs⟩ := h
  let ρ : History (TreeMachine.Cfg p.registers) (TreeMachine.Action p.registers) :=
    History.nil (TreeMachine.Cfg.init p.registers x)
  have hzero (a : ν) : p.register a ≠ 0 := by simp [register, Fin.ext_iff]
  have hempty : p.empty ≠ 0 := by simp [empty, Fin.ext_iff]
  obtain ⟨σ, hcopy, hf, hσ⟩ := (Expr.var ()).exec_assign_history (p.register p.input)
    (fun _ ↦ (0 : Fin p.registers)) p.empty (FinEnum.card ν + 2)
    (by simp [registers, Expr.slots]) (by simp) (by simp [empty]) ρ
    (by simp [ρ, TreeMachine.input_get_of_ne, hempty])
  have hinit : σ.last.regs ∘ p.register = Function.update (fun _ ↦ Tree.nil) p.input x := by
    funext j
    simpa [ρ, Function.update_apply, p.register_injective.eq_iff,
      TreeMachine.input_get_of_ne x (hzero j)] using hf (p.register j) (p.register_lt j)
  have hz : σ.last.regs p.empty = .nil := by
    simpa [ρ, Ne.symm (p.register_ne_empty p.input), TreeMachine.input_get_of_ne x hempty]
      using hf p.empty (by simp [empty])
  obtain ⟨τ, hb, hτ, hzτ, hpeak⟩ := hr.compile_history p.register p.register_injective p.empty
    (FinEnum.card ν + 2) (by simp [registers]) p.register_lt (by simp [empty])
    p.register_ne_empty σ hinit hz
  obtain ⟨υ, he, hυ, hout⟩ := p.result.exec_assign_history 0 p.register p.empty
    (FinEnum.card ν + 2) (by simp [registers]) p.register_lt (by simp [empty]) τ hzτ
  apply TreeMachine.Program.computesInUnitTimeAndSpace_of_exec
    (p := p.code) (hcopy.bind (hb.bind he)) ht
  · simpa [hτ, hy] using hυ 0 (by simp)
  · apply (TreeMachine.configSup_mass_le_sum υ).trans
    calc
      _ ≤ ∑ _ : Fin p.registers, (space + 2) := Finset.sum_le_sum fun j _ ↦ by
        have h₁ := hσ j
        have h₂ := hpeak j
        have h₃ := hout j
        simp only [hτ] at h₃
        have hi : (ρ.last.regs j).size ≤ space := by
          by_cases hj : j = 0
          · simpa [ρ, hj] using hx
          · simpa [ρ, TreeMachine.input_get_of_ne x hj] using
              Nat.succ_le_of_lt ((Tree.size_pos x).trans_le hx)
        simp only [ρ, History.configSup_nil, History.last_nil, Expr.maxSize,
          Function.comp_apply, TreeMachine.Cfg.init_regs, TreeMachine.input_get] at h₁ hi
        omega
      _ = _ := by simp

/-- Prove the readable source program once; its generated machine computes the same output. -/
theorem compile_correct {p : Procedure ν} {x y : Tree} (h : p.Exec x y) :
    ∃ n, p.compile.Halted (p.compile.run x n) ∧ (p.compile.run x n).2.regs 0 = y := by
  obtain ⟨s, ⟨n, b, hr⟩, hy⟩ := h
  have h : p.Bounded x y (2 + (n + p.result.assignSteps))
      (max x.size (max b (p.result.maxSize s))) :=
    ⟨n, s, b, hr, hy, le_rfl, le_max_left ..,
      (le_max_left ..).trans (le_max_right ..), (le_max_right ..).trans (le_max_right ..)⟩
  obtain ⟨n, hh, ho, _, _⟩ := h.compile.exists_halted
  exact ⟨n, hh, ho⟩

end Procedure

namespace Code

/-- The static register count for a closed monadic program. -/
def registers (p : Code Value) : ℕ := p.source.close.registers

instance (p : Code Value) : NeZero p.registers := inferInstanceAs (NeZero p.source.close.registers)

/-- Compile an ordinary monadic definition; all source names and registers are chosen here. -/
def compile (p : Code Value) :
    TreeMachine Id p.registers (p.source.close.code.State ⊕ p.source.close.code.Exit) :=
  p.source.close.compile

/-- A source-level proof for a monadic definition also proves its compiled machine correct. -/
theorem compile_correct {p : Code Value} {x y : Tree} (h : p.Computes x y) :
    ∃ n, p.compile.Halted (p.compile.run x n) ∧ (p.compile.run x n).2.regs 0 = y :=
  Procedure.compile_correct (Procedure.close_correct h)

/-- Prove resource bounds on the readable monadic program. The input must fit as well;
the returned value already fits by the source bound. Four transitions cover input/output copies. -/
theorem Bounded.compile {p : Code Value} {x y : Tree} {time space : ℕ}
    (h : p.Bounded 1 (Function.update (fun _ ↦ Tree.nil) 0 x) time space
      (fun v s ↦ v.eval s = y)) (hx : x.size ≤ space) :
    p.compile.ComputesInUnitTimeAndSpace x y (time + 4) (p.registers * (space + 2)) := by
  obtain ⟨n, s, b, hr, hn, hb, ho⟩ := h
  apply Procedure.Bounded.compile (Procedure.close_bounded ?_)
  refine ⟨n, s, b, hr, ?_, ?_, hx, hb, ?_⟩
  · simpa only [source, Value.eval_expression] using ho
  · have ha := (p.build 1).1.assignSteps_le
    change 2 + (n + (p.build 1).1.expression.assignSteps) ≤ time + 4
    omega
  · have hpos := (Tree.size_pos x).trans_le hx
    have hs := hr.size_le (by
      intro i
      by_cases hi : i = 0 <;> simp [hi] <;> omega) hb
    change (p.build 1).1.expression.maxSize s ≤ space
    rw [Value.maxSize_expression]
    cases (p.build 1).1 with
    | nil => exact Nat.succ_le_of_lt hpos
    | var i => exact hs i

end Code

end Complexity.TreeProgram
