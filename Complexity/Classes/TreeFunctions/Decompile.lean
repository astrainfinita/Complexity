/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Tree programs for polynomial-time tree functions

A function in `FP .sizeCostTree` is computed by a finite deterministic tree machine. The program
built here runs that machine step by step: the loop state is the machine configuration, coded as
its control state followed by the list of its registers. One round tests the roots that the
transition observes at fixed paths of this code, then builds the next configuration's code from
subtrees of the current one in one assignment, so a round costs a constant depending only on the
machine. The loop domain is restricted to configurations from which the machine halts, and the
number of steps until it halts is the loop measure. The root tests are
`Source.exists_hasProgramInO_dispatch` and the builds `Source.exists_hasProgramInO_assemble`.

The one-hot code of control states and the list code of register banks are the current choices,
not decisions; the names are provisional.
-/

@[expose] public section

namespace Complexity.TreeMachine.Decompile

open TreeProgram TreeProgram.Source

variable {k : ℕ}

/-- The code of a register bank is that of the list of its registers. -/
@[instance_reducible]
def cfgEncoding (k : ℕ) : UniqueEncoding Tree (Cfg k) :=
  UniqueEncoding.ofEquiv inferInstance ⟨Cfg.regs, Cfg.mk, fun _ => rfl, fun _ => rfl⟩

attribute [local instance] cfgEncoding

/-- The code of a register bank, as the list of its registers. -/
theorem encode_cfg (c : Cfg k) : ⌜c⌝ₜ = ⌜List.ofFn c.regs⌝ₜ := rfl

/-- A configuration's code stores its registers with one node per register and a final leaf. -/
theorem size_encode_cfg (c : Cfg k) : ⌜c⌝ₜ.size = c.mass + k + 1 := by
  rw [encode_cfg, size_encode_list]
  simp [Cfg.mass, List.sum_ofFn]

/-- The path to entry `j` of a list's code. -/
def listPath (j : ℕ) : List Bool := List.replicate j true ++ [false]

/-- The subtree at `listPath j` of a list's code is the code of entry `j`. -/
theorem subtree_listPath {γ : Type*} [UniqueEncoding Tree γ] (l : List γ) (j : ℕ)
    (hj : j < l.length) : ⌜l⌝ₜ.subtree (listPath j) = ⌜l[j]⌝ₜ := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simp [listPath, Tree.subtree, encode_prod]
    | succ j =>
      have := ih j (by simpa using hj)
      simp only [listPath, List.replicate_succ, List.cons_append] at this ⊢
      simpa [Tree.subtree, encode_prod] using this

/-- `subtree_listPath` for a list of all values of a function on `Fin m`. -/
theorem subtree_listPath_ofFn {γ : Type*} [UniqueEncoding Tree γ] {m : ℕ} (g : Fin m → γ)
    (j : Fin m) : ⌜List.ofFn g⌝ₜ.subtree (listPath j) = ⌜g j⌝ₜ := by
  simpa using subtree_listPath (List.ofFn g) j (by simp)

/-- The path to register `i` in a configuration's code. -/
abbrev regPath (i : ℕ) : List Bool := true :: listPath i

/-- The path to the bit `j` of the control state in a configuration's code. -/
abbrev statePath (j : ℕ) : List Bool := false :: listPath j

/-- The paths whose roots a step inspects: the state bits and the register roots. -/
def rootPaths (n k : ℕ) : List (List Bool) :=
  List.ofFn (fun j : Fin n => statePath j) ++ List.ofFn (fun i : Fin k => regPath i)

section Machine

variable {Q : Type} {n : ℕ} (e : Q ≃ Fin n)

/-- The one-hot bits of a control state. -/
def stateBits (q : Q) : Fin n → Bool := fun j => decide (e q = j)

/-- Distinct control states have distinct bits. -/
theorem stateBits_injective : Function.Injective (stateBits e) := by
  intro q q' h
  have := congrFun h (e q')
  simpa [stateBits] using this

/-- The code of the bits of a control state has at most `4 * n + 1` nodes. -/
theorem size_encode_stateBits (q : Q) : ⌜stateBits e q⌝ₜ.size ≤ 4 * n + 1 := by
  rw [encode_fin_function, size_encode_list, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  have : ∑ j, ⌜stateBits e q j⌝ₜ.size ≤ ∑ _j : Fin n, 3 :=
    Finset.sum_le_sum fun j _ => size_encode_bool_le _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  simp only [Function.comp_apply]
  omega

/-- The control state whose bits begin a list of bits, or `q₀`. -/
noncomputable def decodeState (q₀ : Q) (l : List Bool) : Q :=
  open Classical in
  if h : ∃ q, List.ofFn (stateBits e q) = l.take n then h.choose else q₀

/-- The bits of a control state, followed by any bits, decode to that state. -/
theorem decodeState_append (q₀ q : Q) (l : List Bool) :
    decodeState e q₀ (List.ofFn (stateBits e q) ++ l) = q := by
  have hq : ∃ q', List.ofFn (stateBits e q') = (List.ofFn (stateBits e q) ++ l).take n :=
    ⟨q, by simp⟩
  simp only [decodeState, hq, ↓reduceDIte]
  apply stateBits_injective e
  apply List.ofFn_injective
  simpa using hq.choose_spec

variable {e}

variable (n) in
/-- The observation following the state bits in a list of bits. -/
def decodeObs (l : List Bool) : Fin k → Bool := fun i => l.getD (n + i) false

/-- The observation after the bits of a control state is read back. -/
theorem decodeObs_append (q : Q) (o : Fin k → Bool) :
    decodeObs n (List.ofFn (stateBits e q) ++ List.ofFn o) = o := by
  funext i
  simp [decodeObs, List.getD_eq_getElem?_getD]

variable [UniqueEncoding Tree Q]

/-- The subtree at `regPath i` of a configuration's code is register `i`. -/
theorem subtree_regPath (x : Q × Cfg k) (i : Fin k) : ⌜x⌝ₜ.subtree (regPath i) = x.2.regs i := by
  obtain ⟨q, c⟩ := x
  simpa [Tree.subtree, encode_cfg] using subtree_listPath_ofFn c.regs i

/-- The root at `statePath j` of a configuration's code is bit `j` of its state. -/
theorem root_statePath (hQ : ∀ q, ⌜q⌝ₜ = ⌜stateBits e q⌝ₜ) (x : Q × Cfg k) (j : Fin n) :
    (⌜x⌝ₜ.subtree (statePath j)).root = stateBits e x.1 j := by
  obtain ⟨q, c⟩ := x
  have := subtree_listPath_ofFn (stateBits e q) j
  simp only [encode_fin_function] at hQ
  simp [Tree.subtree, hQ, this]

/-- The roots at `rootPaths` are the state bits followed by the observation. -/
theorem map_rootPaths (hQ : ∀ q, ⌜q⌝ₜ = ⌜stateBits e q⌝ₜ) (x : Q × Cfg k) :
    (rootPaths n k).map (fun p => (⌜x⌝ₜ.subtree p).root) =
      List.ofFn (stateBits e x.1) ++ List.ofFn (observe x.2 : Fin k → Bool) := by
  simp only [rootPaths, List.map_append, List.map_ofFn]
  congr 1
  · congr 1; funext j; exact root_statePath hQ x j
  · congr 1; funext i; simp only [Function.comp_apply, subtree_regPath]; rfl

/-- The assembly of register `i` after an action, from the code of the configuration before. -/
def assembly : Action k → Fin k → Assembly
  | .nop, i => .read (regPath i)
  | .left d j, i => if i = d then .read (regPath j ++ [false]) else .read (regPath i)
  | .right d j, i => if i = d then .read (regPath j ++ [true]) else .read (regPath i)
  | .pair d j l, i =>
    if i = d then .pair (.read (regPath j)) (.read (regPath l)) else .read (regPath i)

/-- `assembly a i` builds register `i` after the action `a`. -/
theorem eval_assembly (a : Action k) (x : Q × Cfg k) (i : Fin k) :
    (assembly a i).eval ⌜x⌝ₜ = a.eval x.2.regs i := by
  have hr (j : Fin k) (p : List Bool) :
      (Assembly.read (regPath j ++ p)).eval ⌜x⌝ₜ = (x.2.regs j).subtree p := by
    simp only [Assembly.eval, Tree.subtree_append, subtree_regPath]
  have hr' (j : Fin k) : (Assembly.read (regPath j)).eval ⌜x⌝ₜ = x.2.regs j := by
    simpa [Tree.subtree] using hr j []
  cases a with
  | nop => exact hr' i
  | left d j =>
    by_cases h : i = d
    · subst h; simpa [assembly, Tree.subtree] using hr j [false]
    · simpa [assembly, h] using hr' i
  | right d j =>
    by_cases h : i = d
    · subst h; simpa [assembly, Tree.subtree] using hr j [true]
    · simpa [assembly, h] using hr' i
  | pair d j l =>
    by_cases h : i = d
    · subst h; simp [assembly, Assembly.eval, subtree_regPath]
    · simpa [assembly, h] using hr' i

variable (M : TreeMachine Id k Q)

/-- One step from a configuration whose state and observation are known. -/
def leafStep (q : Q) (o : Fin k → Bool) (x : Q × Cfg k) : Q × Cfg k :=
  if M.halt q then x else apply (M.transition q o).run x

/-- A step from a known state and observation copies or rebuilds parts of the configuration's
code in one assignment. -/
theorem exists_hasProgramInO_leafStep (q : Q) (o : Fin k → Bool) :
    ∃ p, Internal.HasProgramInO (leafStep M q o) p (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  by_cases h : M.halt q
  · refine ⟨_, (Internal.HasProgramInO.identity.congr ?_).mono Dominated.zero Dominated.zero⟩
    funext x; simp [leafStep, h]
  · apply exists_hasProgramInO_assemble (.pair (.const ⌜(M.transition q o).run.1⌝ₜ)
      (Assembly.list (List.ofFn (assembly (M.transition q o).run.2))))
    intro x
    simp only [leafStep, h, Bool.false_eq_true, ↓reduceIte, Assembly.eval, Assembly.eval_list,
      Controller.apply_prod, encode_prod, encode_cfg, Cfg.apply_regs, List.map_ofFn]
    congr 3
    funext i
    exact eval_assembly _ x i

variable {M}

/-- A step tests the state bits and the register roots, then runs the selected leaf. -/
theorem exists_hasProgramInO_step (hQ : ∀ q, ⌜q⌝ₜ = ⌜stateBits e q⌝ₜ) :
    ∃ p, Internal.HasProgramInO (M.step : Q × Cfg k → Q × Cfg k) p (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) := by
  obtain ⟨p, hp⟩ := exists_hasProgramInO_dispatch (rootPaths n k)
    (fun l => leafStep M (decodeState e M.q₀ l) (decodeObs n l))
    (fun l => exists_hasProgramInO_leafStep M _ _)
  refine ⟨p, hp.congr (funext fun x => ?_)⟩
  simp only [map_rootPaths hQ, decodeState_append, decodeObs_append, leafStep, step_eq]

/-- Whether the machine runs is read from the state bits. -/
theorem exists_hasProgramInO_running (hQ : ∀ q, ⌜q⌝ₜ = ⌜stateBits e q⌝ₜ) :
    ∃ p, Internal.HasProgramInO (fun x : Q × Cfg k => !M.halt x.1) p (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) := by
  obtain ⟨p, hp⟩ := exists_hasProgramInO_dispatch (rootPaths n k)
    (fun l (_ : Q × Cfg k) => !M.halt (decodeState e M.q₀ l))
    (fun l => ⟨_, (Internal.HasProgramInO.const _).mono (.refl _)
      (Dominated.one fun _ => Tree.size_pos _)⟩)
  refine ⟨p, hp.congr (funext fun x => ?_)⟩
  simp only [map_rootPaths hQ, decodeState_append]

/-- The output register is a subtree of a configuration's code. -/
theorem hasProgramInO_output [NeZero k] :
    Internal.HasProgramInO (fun x : Q × Cfg k => x.2.regs 0)
      (fun v => Code.eval (v.expression.subtree (regPath 0))) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  Internal.HasProgramInO.subtree (regPath 0) fun x => (subtree_regPath x 0).symm

end Machine

section Loop

variable {Q : Type} (M : TreeMachine Id k Q)

/-- The configurations from which `M` halts. -/
abbrev HaltingCfg := {x : Q × Cfg k // ∃ i, M.Halted (M.runFrom x i)}

variable {M}

open Classical in
/-- The number of steps until the run from a configuration halts. -/
noncomputable def haltTime (y : HaltingCfg M) : ℕ := Nat.find y.2

/-- The run halts at `haltTime`. -/
theorem halted_runFrom_haltTime (y : HaltingCfg M) : M.Halted (M.runFrom y.1 (haltTime y)) := by
  classical exact Nat.find_spec y.2

/-- `haltTime` is the first step at which the run halts. -/
theorem haltTime_le (y : HaltingCfg M) {m : ℕ} (h : M.Halted (M.runFrom y.1 m)) :
    haltTime y ≤ m := by
  classical exact Nat.find_min' y.2 h

/-- Every halted configuration of the run is the one at `haltTime`. -/
theorem runFrom_eq_runFrom_haltTime (y : HaltingCfg M) {m : ℕ} (h : M.Halted (M.runFrom y.1 m)) :
    M.runFrom y.1 m = M.runFrom y.1 (haltTime y) :=
  M.runFrom_eq_of_halted _ (halted_runFrom_haltTime y) (haltTime_le y h)

/-- One step keeps a configuration among those from which `M` halts. -/
def HaltingCfg.step (y : HaltingCfg M) : HaltingCfg M :=
  ⟨M.step y.1, haltTime y, by
    rw [← M.runFrom_succ, M.runFrom_eq_of_halted _ (halted_runFrom_haltTime y) (Nat.le_succ _)]
    exact halted_runFrom_haltTime y⟩

/-- A step of a running machine brings the halting step closer. -/
theorem haltTime_step_lt (y : HaltingCfg M) (h : (!M.halt y.1.1) = true) :
    haltTime y.step < haltTime y := by
  have h0 : haltTime y ≠ 0 := by
    intro h0
    have := halted_runFrom_haltTime y
    rw [h0, Controller.runFrom_zero] at this
    simp_all [Controller.Halted]
  have : M.Halted (M.runFrom y.step.1 (haltTime y - 1)) := by
    rw [HaltingCfg.step, ← M.runFrom_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    exact halted_runFrom_haltTime y
  have := haltTime_le y.step this
  omega

/-- The largest configuration code reached before halting. -/
noncomputable def peakSize [UniqueEncoding Tree Q] (y : HaltingCfg M) : ℕ :=
  (Finset.range (haltTime y + 1)).sup fun i => ⌜M.runFrom y.1 i⌝ₜ.size

/-- Every configuration of the run, also after it halts, fits in `peakSize`. -/
theorem size_le_peakSize [UniqueEncoding Tree Q] (y : HaltingCfg M) (i : ℕ) :
    ⌜M.runFrom y.1 i⌝ₜ.size ≤ peakSize y := by
  rcases le_or_gt i (haltTime y) with hi | hi
  · exact Finset.le_sup (f := fun i => ⌜M.runFrom y.1 i⌝ₜ.size) (by simp; omega)
  · rw [M.runFrom_eq_of_halted _ (halted_runFrom_haltTime y) hi.le]
    exact Finset.le_sup (f := fun i => ⌜M.runFrom y.1 i⌝ₜ.size) (by simp)

variable [NeZero k]

/-- The output register when the run halts. -/
noncomputable def output (y : HaltingCfg M) : Tree := (M.runFrom y.1 (haltTime y)).2.regs 0

/-- The output can be read at any step at which the run has halted. -/
theorem output_eq (y : HaltingCfg M) {m : ℕ} (h : M.Halted (M.runFrom y.1 m)) :
    output y = (M.runFrom y.1 m).2.regs 0 := by
  rw [output, runFrom_eq_runFrom_haltTime y h]

/-- The halting run's output follows one step at a time. -/
theorem output_equation (y : HaltingCfg M) :
    output y = if (!M.halt y.1.1) then output y.step else y.1.2.regs 0 := by
  cases hy : M.halt y.1.1
  · simp only [Bool.not_false, ↓reduceIte]
    rw [output_eq y (m := haltTime y.step + 1)]
    · rw [M.runFrom_succ]; rfl
    · rw [M.runFrom_succ]; exact halted_runFrom_haltTime y.step
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact output_eq y (m := 0) hy

variable [UniqueEncoding Tree Q] {n : ℕ} {e : Q ≃ Fin n}

/-- The halting run, step by step, with one round per step of `M`. -/
theorem exists_hasProgramInO_output (hQ : ∀ q, ⌜q⌝ₜ = ⌜stateBits e q⌝ₜ) :
    ∃ p, Internal.HasProgramInO (output : HaltingCfg M → Tree) p
      (fun y => 1 + (haltTime y * 1 + 1) + 1) peakSize := by
  obtain ⟨qc, hc⟩ := exists_hasProgramInO_running (M := M) hQ
  obtain ⟨qs, hs⟩ := exists_hasProgramInO_step (M := M) hQ
  have hc' := hc.map_input (Subtype.val : HaltingCfg M → Q × Cfg k) (fun _ => rfl)
  have hs' : Internal.HasProgramInO (HaltingCfg.step : HaltingCfg M → HaltingCfg M) qs _ _ :=
    Internal.HasProgramInO.of_encode (g := fun y : HaltingCfg M => M.step y.1) (fun _ => rfl)
      (hs.map_input (Subtype.val : HaltingCfg M → Q × Cfg k) (fun _ => rfl))
  have hd' := (hasProgramInO_output (Q := Q)).map_input
    (Subtype.val : HaltingCfg M → Q × Cfg k) (fun _ => rfl)
  have hpeak : Dominated
      (fun z : {p : HaltingCfg M × HaltingCfg M // ∃ i, p.2.1 = M.runFrom p.1.1 i} =>
        ⌜z.1.2.1⌝ₜ.size) (fun z => peakSize z.1.1) := by
    refine Dominated.of_le fun z => ?_
    obtain ⟨i, hi⟩ := z.2
    rw [hi]
    exact size_le_peakSize z.1.1 i
  exact ⟨_, by
    source_fun_prop using loop (test := fun y : HaltingCfg M => !M.halt y.1.1)
      (next := HaltingCfg.step) (finish := fun y : HaltingCfg M => y.1.2.regs 0)
      (invariant := fun x y => ∃ i, y.1 = M.runFrom x.1 i) (measure := haltTime)
      (step := fun _ => 1) (stop := fun _ => 1) (space := peakSize)
    case equation => exact output_equation
    case initial => exact fun x => ⟨0, rfl⟩
    case next_state =>
      rintro x y ⟨i, hi⟩ -
      exact ⟨i + 1, by rw [M.runFrom_succ', ← hi]; rfl⟩
    case decreases => exact fun x y _ h => haltTime_step_lt y h
    case step_pos | stop_pos => exact fun _ => Nat.one_pos
    all_goals exact hpeak⟩

end Loop

end Complexity.TreeMachine.Decompile

namespace Complexity.TreeMachine

open TreeProgram TreeProgram.Source Decompile

attribute [local instance] cfgEncoding

/-- A function computed in polynomial size-charged time by a finite tree machine has a tree
program polynomial in the input code size: the program runs the machine step by step. -/
theorem exists_hasProgramIn_of_mem_fp {α β : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] {f : α → β} (hf : f ∈ FP .sizeCostTree) :
    ∃ program, HasProgramIn f program (IsPoly fun x => ⌜x⌝ₜ.size)
      (IsPoly fun x => ⌜x⌝ₜ.size) := by
  obtain ⟨t, s, ⟨R, ⟨k, hk, Q, hQf, M, rfl⟩, h⟩, ht⟩ := FP.mem_iff_isPoly.1 hf
  have hM (a : α) : M.ComputesWithin ⌜a⌝ₜ ⌜f a⌝ₜ (t ⌜a⌝ₜ.size) (s ⌜a⌝ₜ.size) :=
    Encoding.Computes.iff_of_uniqueEncoding.mp h a
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Q
  let _ : UniqueEncoding Tree Q :=
    UniqueEncoding.ofInjective inferInstance (stateBits e) (stateBits_injective e)
  obtain ⟨ql, hl⟩ := exists_hasProgramInO_output (M := M) (e := e) fun _ => rfl
  let init (a : α) : HaltingCfg M := ⟨M.init ⌜a⌝ₜ, (hM a).terminates⟩
  obtain ⟨qi, hi⟩ := exists_hasProgramInO_assemble (f := init) (.pair (.const ⌜M.q₀⌝ₜ)
    (Assembly.list (List.ofFn fun i : Fin k => if i = 0 then .read [] else .const .nil))) <| by
    intro a
    simp only [Assembly.eval, Assembly.eval_list, List.map_ofFn, init,
      UniqueEncoding.encode_subtype, Controller.init, hasConfig_init, encode_prod, encode_cfg,
      Cfg.init_regs]
    congr 3
    funext i
    by_cases hi : i = 0
    · subst hi; simp [Assembly.eval, Tree.subtree]
    · simp [Assembly.eval, hi]
  have hfeq (a : α) : ⌜f a⌝ₜ = ⌜output (init a)⌝ₜ := by
    obtain ⟨m, -, hm, ho, -, -⟩ := (hM a).exists_haltsAt
    rw [Tree.encode_self, output_eq (init a) hm.1]
    exact ho.symm
  refine ⟨_, ((hi.comp hl).of_encode hfeq).hasProgramIn ?_ ?_⟩
  · refine ((ht.comp IsPoly.refl).add (IsPoly.const 4)).of_dominated
      (Dominated.of_le fun a => ?_)
    obtain ⟨m, hmt, hm, -⟩ := (hM a).exists_haltsAt
    have := haltTime_le (init a) hm.1
    omega
  · refine (IsPoly.refl.add ((ht.comp IsPoly.refl).add
      (IsPoly.const (4 * n + 2 * k + 3)))).of_dominated (Dominated.of_le fun a => ?_)
    refine max_le (by omega) (Finset.sup_le fun i _ => ?_)
    have hm := (hM a).mass_le_mass_add_time i
    have hi := Cfg.mass_init_le (k := k) ⌜a⌝ₜ
    have hq : ⌜(M.run ⌜a⌝ₜ i).1⌝ₜ.size ≤ 4 * n + 1 := size_encode_stateBits e _
    have hc := size_encode_cfg (M.run ⌜a⌝ₜ i).2
    rw [Controller.run] at hm hq hc
    simp only [init, Prod.size_encode_eq]
    omega

end Complexity.TreeMachine
