/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Resources.Circuit.Unroll
import Complexity.Resources.Circuit.Composition
import Complexity.Classes.Functions.Basic
open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.CircuitComposition

-- The structural recursion entry keeps the previously selected callback programs.
example : programCompFn =
    Recursion.code programCompTest programCompNextFn programCompFinishFn programCompResume := rfl

-- Recursive certification keeps the explicitly selected terminal callback.
example : programRelabelFn = Recursion.code programRelabelTest programRelabelNextFn
    programRelabelFinishFn programRelabelResume := rfl
example : HasProgram relabelFinishFn programRelabelFinishFn
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := hasProgram_relabelFinishFn

def rewire (x : RelabelInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.k, x.m, x.circuit.relabel x.wires⟩
example := (by source_fun_prop : HasProgram rewire _ _ _)

def pipeline (x : CompInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.n, x.k, x.first.comp x.second⟩
example := (by source_fun_prop : HasProgram pipeline _ _ _)

def preserve (x : Σ n, Σ m, Circuit .booleanAlgebra n m) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.1 + x.2.1, x.2.2.keepInputs⟩
example := (by source_fun_prop : HasProgram preserve _ _ _)

def layers (x : Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2, x.1, x.2.1.unroll x.2.2⟩
example := (by source_fun_prop : HasProgram layers _ _ _)

/-- Rewiring an already represented set of inputs, retaining the same input count. -/
def rewireStored (x : Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.2.1, x.2.2.1.relabel x.2.2.2⟩

abbrev StoredRelabelInput := Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)

/-- Compose the selected implementation; only the mathematical size relations remain. -/
@[source] theorem hasProgram_rewireStored : HasProgram rewireStored hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 7) (fun x => ⌜x⌝ₜ.size ^ 4) := by
  abstract_hole program using programRewireStored
  let u (x : Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)) : RelabelInput :=
    ⟨x.1, x.2.1, x.1, x.2.2.1, x.2.2.2⟩
  let S (x : Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)) := ⌜x⌝ₜ.size
  let o x := ⌜relabelFn (u x)⌝ₜ.size
  have hpos x : 0 < S x := Tree.size_pos _
  have hR : Dominated (relabelScale ∘ u) S := Dominated.of_le_mul 6 fun x => by
    rcases x with ⟨n, m, c, w⟩
    have hc : ⌜c⌝ₜ.size ≤ S ⟨n, m, c, w⟩ := by
      simp only [S, Sigma.encode_mk, size_encode_prod]
      omega
    have hw : ⌜w⌝ₜ.size ≤ S ⟨n, m, c, w⟩ := by
      simp only [S, Sigma.encode_mk, size_encode_prod]
      omega
    have hn := (card_le_size_encode_fin_function w).trans hw
    have hm := c.outputs_le_size_encode.trans hc
    have hg := c.size_le_size_encode.trans hc
    have hp := hpos ⟨n, m, c, w⟩
    dsimp [Function.comp_def, u, relabelScale]
    omega
  have ho : Dominated o (fun x => S x ^ 2) :=
    (Dominated.comp (Dominated.of_le_mul 100 size_encode_relabelFn_le) u).trans (hR.pow 2)
  have hS : Dominated S (fun x => S x ^ 4) :=
    Dominated.of_le fun x => Nat.le_self_pow (by decide) _
  have ho4 := ho.trans (Dominated.of_le fun x => Nat.pow_le_pow_right (hpos x) (by decide : 2 ≤ 4))
  fill_hole program in source_fun_prop
  · simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
      | exact hR.pow 7
  · have hp : Dominated (fun x => 2 * S x + o x + 2 + relabelScale (u x) ^ 4)
        (fun x => S x ^ 4) := by
      simp only [Dominated.add_iff]
      exact ⟨⟨⟨hS.const_mul_left 2, ho4⟩,
        Dominated.const_of_pos 2 fun x => Nat.pow_pos (hpos x)⟩, hR.pow 4⟩
    apply hp.mono_left
    rintro ⟨n, m, c, w⟩
    dsimp only [S, o, u, Function.comp_apply, relabelFn]
    simp only [Sigma.encode_mk, RelabelInput.encode_mk, size_encode_prod]
    omega

theorem rewireStored_ftisp :
    rewireStored ∈ FTISP .tree (fun n => n ^ 7) (fun n => n ^ 4) :=
  hasProgram_rewireStored.mem_ftisp_pow (by decide)

/-- Unary storage makes the number of generated layers bounded by input size. -/
def layersStored (x : Σ n, Circuit .booleanAlgebra (n + 1) n × List Unit) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2.length, x.1, x.2.1.unroll x.2.2.length⟩

@[source] theorem hasProgram_layersStored : HasProgram layersStored hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 18) (fun x => ⌜x⌝ₜ.size ^ 8) := by
  abstract_hole program using programLayersStored
  let S (x : Σ n, Circuit .booleanAlgebra (n + 1) n × List Unit) := ⌜x⌝ₜ.size
  let u (x : Σ n, Circuit .booleanAlgebra (n + 1) n × List Unit) : UnrollInput :=
    ⟨x.1, x.2.1, x.2.2.length⟩
  have hS x : 0 < S x := Tree.size_pos _
  have hc : Dominated (fun x => ⌜x.2.1⌝ₜ.size) S := Dominated.of_le fun x => by
    rcases x with ⟨n, c, xs⟩; simp only [S, Sigma.encode_mk, size_encode_prod]; omega
  have hxs : Dominated (fun x => ⌜x.2.2⌝ₜ.size) S := Dominated.of_le fun x => by
    rcases x with ⟨n, c, xs⟩; simp only [S, Sigma.encode_mk, size_encode_prod]; omega
  have hn : Dominated (fun x => x.1) S := hc.mono_left fun x => x.2.1.outputs_le_size_encode
  have hg : Dominated (fun x => x.2.1.size) S := hc.mono_left fun x => x.2.1.size_le_size_encode
  have ht : Dominated (fun x => x.2.2.length) S := hxs.mono_left fun x => length_le_codeSize _
  have hcn := Dominated.size_encode_nat hn hS
  have hct := Dominated.size_encode_nat ht hS
  have hcnt := Dominated.size_encode_nat (hn.add_same ht) hS
  have hR : Dominated (unrollScale ∘ u) (fun x => S x ^ 2) := by
    have hm := (ht.add_same (Dominated.one hS)).mul hg
    simp only [← pow_two] at hm
    simp only [Function.comp_def, u, unrollScale, Dominated.add_iff]
    exact ⟨⟨⟨Dominated.le_pow (hn.const_mul_left 2) (by decide), ht.le_pow (by decide)⟩, hm⟩,
      Dominated.const_of_pos 2 (fun x => Nat.pow_pos (hS x))⟩
  have hu : Dominated (fun x => ⌜u x⌝ₜ.size) S := by
    simp only [u, Sigma.encode_mk, size_encode_prod, Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos 1 hS, hcn⟩,
      ⟨⟨Dominated.const_of_pos 1 hS, hc⟩, hct⟩⟩
  have htime := hR.pow 9
  have hpeak := hR.pow 4
  simp only [← pow_mul, Function.comp_def, u] at htime hpeak
  have hout := (Dominated.comp hasProgram_unroll.size_encode u).trans
    ((hu.le_pow (by decide : 0 < 8)).max_same hpeak)
  simp only [Function.comp_def, u] at hout
  fill_hole program in source_fun_prop
  all_goals
    simp only [Sigma.encode_mk, size_encode_prod, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hS x))
    | exact Dominated.le_pow (g := S) (by first | assumption | exact Dominated.refl _) (by decide)

theorem layersStored_ftisp :
    layersStored ∈ FTISP .tree (fun n => n ^ 18) (fun n => n ^ 8) :=
  hasProgram_layersStored.mem_ftisp_pow (by decide)

end ComplexityTest.SourceTranslation.CircuitComposition
