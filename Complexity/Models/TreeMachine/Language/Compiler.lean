/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Expression
public import Complexity.Models.TreeMachine.Language.Bounds
public import Complexity.Control.Program.Loop

/-! # Compiling structured tree programs

Source variables have fixed slots. Expression temporaries are reused across statements and
loop iterations; the number of registers depends only on the program. Source runs
transport their value, a unit-time bound and bounds on every intermediate register tree.
-/

@[expose] public section

namespace Complexity.TreeProgram

open Controller (History)

variable {ν : Type} {k : ℕ}

/-- Read the result's root, using existing registers directly for atoms. -/
def Expr.test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) : TreeMachine.Program Id k Bool := do
  let i ← e.compile v z b hb
  TreeMachine.Program.root i

theorem Expr.execWithin_test (e : Expr ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + e.slots ≤ k) (s : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hv : ∀ x, (v x).val < b) (hzv : z.val < b) (hz : s.last.regs z = .nil) :
    (e.test v z b hb).ExecWithin TreeMachine.Program.historySemantics s (e.steps + 1)
      fun r t _ ↦ r = (e.eval (s.last.regs ∘ v)).root ∧ t.last.regs ∘ v = s.last.regs ∘ v ∧
        t.last.regs z = .nil ∧ ∀ j, t.configSup (fun c ↦ (c.regs j).size) ≤
          s.configSup (fun c ↦ (c.regs j).size) ⊔ e.maxSize (s.last.regs ∘ v) := by
  refine (e.execWithin_compile v z b hb s hv hzv hz).bindTo_add ?_
  rintro i t ⟨hval, -, hf, hpeak⟩
  refine TreeMachine.Program.execWithinWith_root
    ⟨by rw [hval], ?_, by simpa using (hf z hzv).trans hz, fun j ↦ ?_⟩
  · simpa only [History.last_snoc, TreeMachine.Action.apply_nop, Function.comp_def]
      using funext (fun x ↦ hf (v x) (hv x))
  · rw [TreeMachine.configSup_snoc_nop t (fun c ↦ (c.regs j).size)]
    exact hpeak j

/-- Scratch space shared by all executions of a statement. -/
def Cmd.slots : Cmd ν → ℕ
  | .skip => 0
  | .assign _ e => e.slots
  | .seq p q => max p.slots q.slots
  | .branch e p q => max e.slots (max p.slots q.slots)
  | .while e p => max e.slots p.slots

/-- Compile assignments and root tests, allocating expression temporaries above `b`. -/
def Cmd.compile (p : Cmd ν) (v : ν → Fin k) (z : Fin k) (b : ℕ)
    (hb : b + p.slots ≤ k) : TreeMachine.Program Id k Unit :=
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

/-- Source runs transport their value within their step count, and an independent peak-size
bound. -/
theorem Cmd.Run.execWithin_compile [DecidableEq ν] {p : Cmd ν} {s t : ν → Tree} {n a : ℕ}
    (h : p.Run s n t a) (v : ν → Fin k) (z : Fin k) (b : ℕ) (hb : b + p.slots ≤ k)
    (ρ : History (TreeMachine.Cfg k) (TreeMachine.Action k))
    (hi : Function.Injective v) (hv : ∀ x, (v x).val < b) (hzv : z.val < b)
    (hvz : ∀ x, v x ≠ z) (hρ : ρ.last.regs ∘ v = s) (hz : ρ.last.regs z = .nil) :
    (p.compile v z b hb).ExecWithin TreeMachine.Program.historySemantics ρ n
      fun _ σ _ ↦ σ.last.regs ∘ v = t ∧ σ.last.regs z = .nil ∧
        ∀ j, σ.configSup (fun c ↦ (c.regs j).size) ≤
          ρ.configSup (fun c ↦ (c.regs j).size) ⊔ (a + 2) := by
  induction h generalizing ρ with
  | skip s => exact .ret _ _ _ ⟨hρ, hz, fun _ ↦ le_sup_left⟩
  | assign x e s =>
    refine (e.execWithin_assign (v x) v z b hb ρ hv hzv hz).mono ?_
    rintro _ σ _ ⟨hf, hpeak⟩
    refine ⟨?_, by simpa [Ne.symm (hvz x), hz] using hf z hzv, by simpa only [hρ] using hpeak⟩
    rw [← hρ, ← Function.update_comp_eq_of_injective ρ.last.regs hi]
    exact funext fun y ↦ hf (v y) (hv y)
  | @seq p₁ p₂ s t u n m a₁ a₂ hp hq ihp ihq =>
    refine (ihp _ ρ hρ hz).bindTo_add fun _ σ ⟨hσ, hzσ, hs⟩ ↦ (ihq _ σ hσ hzσ).mono ?_
    rintro _ τ _ ⟨hτ, hzτ, ht⟩
    exact ⟨hτ, hzτ, fun j ↦ by have := hs j; have := ht j; omega⟩
  | @branch_true e p₁ p₂ s t n a he hp ih | @branch_false e p₁ p₂ s t n a he hp ih =>
    refine (e.execWithin_test v z b _ ρ hv hzv hz).bindTo_add ?_
    rintro _ σ ⟨rfl, hσ, hzσ, hs⟩
    simp only [hρ, he, Bool.false_eq_true, ite_true, ite_false]
    refine (ih _ σ (hσ.trans hρ) hzσ).mono ?_
    rintro _ τ _ ⟨hτ, hzτ, hp⟩
    refine ⟨hτ, hzτ, fun j ↦ ?_⟩
    have := hs j
    have := hp j
    simp only [hρ] at *
    omega
  | @while_false e p s he =>
    refine Program.execWithinWith_repeatUntilWith_done
      ((e.execWithin_test v z b _ (ρ.snoc .nop) hv hzv (by simpa using hz)).bindTo ?_)
    rintro _ σ _ ⟨rfl, hσ, hzσ, hs⟩
    simp only [History.last_snoc, TreeMachine.Action.apply_nop, hρ, he, Bool.false_eq_true,
      ite_false]
    refine .ret _ _ _ ⟨rfl, by simpa [hρ] using hσ, hzσ, fun j ↦ ?_⟩
    have := hs j
    simp only [TreeMachine.configSup_snoc_nop ρ (fun c ↦ (c.regs j).size), History.last_snoc,
      TreeMachine.Action.apply_nop, hρ] at this
    omega
  | @while_true e p s t u n m a c he hp hr ihp ihr =>
    refine .mono_budget (Program.execWithinWith_repeatUntilWith_next
      (P := fun τ ↦ τ.last.regs ∘ v = t ∧ τ.last.regs z = .nil ∧
        ∀ j, τ.configSup (fun c ↦ (c.regs j).size) ≤
          ρ.configSup (fun c ↦ (c.regs j).size) ⊔ (max (e.maxSize s) a + 2))
      ((e.execWithin_test v z b _ (ρ.snoc .nop) hv hzv (by simpa using hz)).bindTo_add
        (c := n) ?_) fun τ ⟨hτ, hzτ, hτp⟩ ↦
        (ihr hb τ hτ hzτ).mono fun _ υ _ ⟨hυ, hzυ, hr⟩ ↦
          ⟨hυ, hzυ, fun j ↦ by have := hτp j; have := hr j; omega⟩) (by omega)
    rintro _ σ ⟨rfl, hσ, hzσ, hs⟩
    simp only [History.last_snoc, TreeMachine.Action.apply_nop, hρ, he, ite_true]
    refine (ihp _ σ (by simpa [hρ] using hσ) hzσ).bindTo fun _ τ _ ⟨hτ, hzτ, hp⟩ ↦
      .ret _ _ _ ⟨rfl, hτ, hzτ, fun j ↦ ?_⟩
    have := hs j
    have := hp j
    simp only [TreeMachine.configSup_snoc_nop ρ (fun c ↦ (c.regs j).size), History.last_snoc,
      TreeMachine.Action.apply_nop, hρ] at *
    omega

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
def code (p : Procedure ν) : TreeMachine.Program Id p.registers Unit := do
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
    p.compile.ComputesWithinUnitTime x y time (p.registers * (space + 2)) := by
  obtain ⟨n, s, a, hr, hy, ht, hx, ha, hs⟩ := h
  let ρ : History (TreeMachine.Cfg p.registers) (TreeMachine.Action p.registers) :=
    History.nil (TreeMachine.Cfg.init p.registers x)
  have hzero (a : ν) : p.register a ≠ 0 := by simp [register, Fin.ext_iff]
  have hempty : p.empty ≠ 0 := by simp [empty, Fin.ext_iff]
  refine TreeMachine.Program.computesWithinUnitTime_of_execWithin (p := p.code) (.mono_budget
    (((Expr.var ()).execWithin_assign (p.register p.input) (fun _ ↦ (0 : Fin p.registers)) p.empty
      (FinEnum.card ν + 2) (by simp [registers, Expr.slots]) ρ (by simp) (by simp [empty])
      (by simp [ρ, TreeMachine.input_get_of_ne, hempty])).bindTo_add fun _ σ ⟨hf, hσ⟩ ↦ ?_) ht)
  have hinit : σ.last.regs ∘ p.register = Function.update (fun _ ↦ Tree.nil) p.input x := by
    funext j
    simpa [ρ, Function.update_apply, p.register_injective.eq_iff,
      TreeMachine.input_get_of_ne x (hzero j)] using hf (p.register j) (p.register_lt j)
  have hz : σ.last.regs p.empty = .nil := by
    simpa [ρ, Ne.symm (p.register_ne_empty p.input), TreeMachine.input_get_of_ne x hempty]
      using hf p.empty (by simp [empty])
  refine (hr.execWithin_compile p.register p.empty (FinEnum.card ν + 2) _ σ p.register_injective
    p.register_lt (by simp [empty]) p.register_ne_empty hinit hz).bindTo_add
    fun _ τ ⟨hτ, hzτ, hpeak⟩ ↦ (p.result.execWithin_assign 0 p.register p.empty
      (FinEnum.card ν + 2) _ τ p.register_lt (by simp [empty]) hzτ).mono ?_
  rintro _ υ _ ⟨hυ, hout⟩
  refine ⟨by simpa [hτ, hy] using hυ 0 (by simp), ?_⟩
  apply (TreeMachine.configSup_mass_le_sum υ).trans
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
    p.compile.ComputesWithinUnitTime x y (time + 4) (p.registers * (space + 2)) := by
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
