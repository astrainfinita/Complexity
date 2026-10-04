/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Expression
public import Complexity.Models.TreeMachine.Language.Code
public import Complexity.Models.TreeMachine.Language.Closure
public import Complexity.Models.TreeMachine.Program.Correctness

/-! # Compiling structured tree programs

Source variables have fixed slots. Expression temporaries are reused across statements and
loop iterations; the number of registers depends only on the program. This first compiler
establishes functional correctness. It does not yet transport time or space bounds.
-/

@[expose] public section

namespace Complexity.TreeProgram

variable {ν : Type} {k : ℕ}

/-- Read the result's root, using existing registers directly for atoms. -/
def Expr.test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program k Bool := do
  let i ← e.compile v z b hb
  TreeMachine.Program.root i

theorem Expr.exec_test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (ρ : Fin k → Tree) (hz : ρ z = .nil) :
    ∃ σ, (e.test v z b hb).Exec TreeMachine.Program.semantics ρ (e.steps + 1)
      (e.eval (ρ ∘ v)).root σ ∧ σ ∘ v = ρ ∘ v ∧ σ z = .nil := by
  obtain ⟨σ, i, he, hval, _, hf⟩ := e.exec_compile v z b hb hv hzv ρ hz
  refine ⟨σ, ?_, funext (fun x ↦ hf (v x) (hv x)), (hf z hzv).trans hz⟩
  have ht := TreeMachine.Program.exec_root i σ
  rw [hval] at ht
  exact he.bind ht

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

/-- Source correctness transports to generated code without exposing its control states. -/
theorem Cmd.Exec.compile [DecidableEq ν] {p : Cmd ν} {s t : ν → Tree}
    (h : p.Exec s t) (v : ν → Fin k) (hi : Function.Injective v) (z : Fin k) (b : ℕ)
    (hb : b + p.slots ≤ k) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (hvz : ∀ x, v x ≠ z) (ρ : Fin k → Tree) (hρ : ρ ∘ v = s) (hz : ρ z = .nil) :
    ∃ n σ, (p.compile v z b hb).Exec TreeMachine.Program.semantics ρ n () σ ∧
      σ ∘ v = t ∧ σ z = .nil := by
  induction h generalizing ρ with
  | skip s => exact ⟨0, ρ, Program.Exec.pure _ _ _, hρ, hz⟩
  | assign x e s =>
    obtain ⟨σ, he, hf⟩ := e.exec_assign (v x) v z b hb hv hzv ρ hz
    refine ⟨e.assignSteps, σ, he, ?_, ?_⟩
    · rw [← hρ, ← Function.update_comp_eq_of_injective ρ hi]
      exact funext fun y ↦ hf (v y) (hv y)
    · simpa [Ne.symm (hvz x), hz] using hf z hzv
  | seq hp hq ihp ihq =>
    obtain ⟨n, σ, hp', hσ, hzσ⟩ := ihp (by simp only [Cmd.slots] at hb; omega) ρ hρ hz
    obtain ⟨m, τ, hq', hτ, hzτ⟩ := ihq (by simp only [Cmd.slots] at hb; omega) σ hσ hzσ
    exact ⟨n + m, τ, hp'.bind hq', hτ, hzτ⟩
  | @branch_true e p q s t he hp ih =>
    obtain ⟨σ, ht, hσ, hzσ⟩ := Expr.exec_test e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ hz
    obtain ⟨m, τ, hp', hτ, hzτ⟩ := ih (by simp only [Cmd.slots] at hb; omega)
      σ (hσ.trans hρ) hzσ
    refine ⟨e.steps + 1 + m, τ, ht.bind ?_, hτ, hzτ⟩
    simpa only [hρ, he, Bool.true_eq, ite_true] using hp'
  | @branch_false e p q s t he hq ih =>
    obtain ⟨σ, ht, hσ, hzσ⟩ := Expr.exec_test e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ hz
    obtain ⟨m, τ, hq', hτ, hzτ⟩ := ih (by simp only [Cmd.slots] at hb; omega)
      σ (hσ.trans hρ) hzσ
    refine ⟨e.steps + 1 + m, τ, ht.bind ?_, hτ, hzτ⟩
    simpa only [hρ, he, Bool.false_eq_true, ite_false] using hq'
  | @while_false e p s he =>
    obtain ⟨σ, ht, hσ, hzσ⟩ := Expr.exec_test e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ hz
    refine ⟨e.steps + 1 + 0 + 1, σ,
      Program.Exec.repeatUntilWith_done TreeMachine.Op.nop _ (ht.bind ?_),
      hσ.trans hρ, hzσ⟩
    simp only [hρ, he, Bool.false_eq_true, ite_false]
    exact (Program.Exec.pure TreeMachine.Program.semantics true σ)
  | @while_true e p s t u he hp hr ihp ihr =>
    obtain ⟨σ, ht, hσ, hzσ⟩ := Expr.exec_test e v z b
      (by simp only [Cmd.slots] at hb; omega) hv hzv ρ hz
    obtain ⟨m, τ, hp', hτ, hzτ⟩ := ihp (by simp only [Cmd.slots] at hb; omega)
      σ (hσ.trans hρ) hzσ
    obtain ⟨l, υ, hr', hυ, hzυ⟩ := ihr hb τ hτ hzτ
    refine ⟨e.steps + 1 + (m + 0) + l + 1, υ,
      Program.Exec.repeatUntilWith_next TreeMachine.Op.nop _ (ht.bind ?_) hr', hυ, hzυ⟩
    simp only [hρ, he, ite_true]
    exact hp'.bind (Program.Exec.pure TreeMachine.Program.semantics false τ)

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
  have := (FinEnum.equiv x).isLt
  simp only [register]
  omega

private theorem register_ne_empty (p : Procedure ν) (x : ν) : p.register x ≠ p.empty := by
  intro h
  have := congrArg Fin.val h
  have := (FinEnum.equiv x).isLt
  simp only [register, empty] at *
  omega

/-- The generated register program. User specifications should use `Procedure.Exec`. -/
def code (p : Procedure ν) : TreeMachine.Program p.registers Unit := do
  TreeMachine.Program.copy p.empty (p.register p.input) 0
  p.body.compile p.register p.empty (FinEnum.card ν + 2) (by simp [registers])
  let i ← p.result.compile p.register p.empty (FinEnum.card ν + 2) (by simp [registers])
  TreeMachine.Program.copy p.empty 0 i

/-- A finite tree machine with automatically chosen registers and control states. -/
def compile (p : Procedure ν) : TreeMachine Id p.registers (p.code.State ⊕ p.code.Exit) :=
  p.code.compile

/-- Prove the readable source program once; the generated machine computes the same output. -/
theorem compile_correct {p : Procedure ν} {x y : Tree} (h : p.Exec x y) :
    ∃ n, p.compile.Halted (p.compile.run (TreeMachine.Cfg p.registers _) x n) ∧
      (p.compile.run (TreeMachine.Cfg p.registers _) x n).regs 0 = y := by
  obtain ⟨s, hs, hy⟩ := h
  let ρ := TreeMachine.input (0 : Fin p.registers) x
  let σ := Function.update ρ (p.register p.input) x
  have hzero (a : ν) : p.register a ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [register, Fin.val_zero] at this
    omega
  have hempty : p.empty ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [empty, Fin.val_zero] at this
    omega
  have hinit : σ ∘ p.register = Function.update (fun _ ↦ Tree.nil) p.input x := by
    funext a
    simp only [σ, ρ, Function.comp_apply, Function.update_apply,
      p.register_injective.eq_iff, TreeMachine.input_get_of_ne x (hzero a)]
  have hz : σ p.empty = .nil := by
    simp only [σ, Function.update_of_ne (Ne.symm (p.register_ne_empty p.input)), ρ,
      TreeMachine.input_get_of_ne x hempty]
  have hcopy : (TreeMachine.Program.copy p.empty (p.register p.input) 0).Exec
      TreeMachine.Program.semantics ρ 2 () σ := by
    simpa only [ρ, TreeMachine.input_get] using
      TreeMachine.Program.exec_copy p.empty (p.register p.input) 0 ρ
  obtain ⟨n, τ, hb, hτ, hzτ⟩ := hs.compile p.register p.register_injective p.empty
    (FinEnum.card ν + 2) (by simp [registers]) p.register_lt (by simp [empty])
    p.register_ne_empty σ hinit hz
  obtain ⟨υ, i, he, hval, _⟩ := p.result.exec_compile p.register p.empty
    (FinEnum.card ν + 2) (by simp [registers]) p.register_lt (by simp [empty]) τ hzτ
  have hout : υ i = y := hval.trans ((congrArg p.result.eval hτ).trans hy)
  have hf := TreeMachine.Program.exec_copy p.empty 0 i υ
  exact ⟨2 + (n + (p.result.steps + 2)), TreeMachine.Program.run_output
    (p := p.code) (hcopy.bind (hb.bind (he.bind hf))) (by simpa using hout)⟩

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
    ∃ n, p.compile.Halted (p.compile.run (TreeMachine.Cfg p.registers _) x n) ∧
      (p.compile.run (TreeMachine.Cfg p.registers _) x n).regs 0 = y :=
  Procedure.compile_correct (Procedure.close_correct h)

end Code

end Complexity.TreeProgram
