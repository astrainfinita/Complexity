/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Choice.Probability
import Complexity.Control.Controller
meta import Complexity.Control.Choice

open Complexity Complexity.Choice

-- Successive choices can take different branch indices; they do not share a Reader input.
#guard ((do
    let i ← binaryMultiset (fun i => i)
    let j ← binaryMultiset (fun j => j)
    pure (i, j)) : Multiset (Fin 2 × Fin 2)) =
  ↑([(0, 0), (0, 1), (1, 0), (1, 1)] : List (Fin 2 × Fin 2))

-- Coincident endpoints retain the multiplicity of the two paths.
#guard binaryMultiset (fun _ => true) = ↑[true, true]
#guard (binaryMultiset (fun _ => true)).count true = 2

-- Swapping the two branch labels changes neither the collection nor its multiplicities.
example {α : Type*} (a b : α) :
    binaryMultiset (fun i => if i = 0 then a else b) =
      binaryMultiset (fun i => if i = 0 then b else a) := by
  change a ::ₘ b ::ₘ (0 : Multiset α) = b ::ₘ a ::ₘ 0
  exact Multiset.cons_swap a b 0

-- Under the probabilistic interpretation coincident endpoints instead add their masses.
example : binaryPMF (fun _ => true) = PMF.pure true := by
  exact PMF.map_const _ _

-- Each labelled branch has probability one half.
example (i : Fin 2) : binaryPMF (fun j => j) i = (2 : ENNReal)⁻¹ := by
  simp [binaryPMF, PMF.uniformOfFintype_apply]

-- Two separately interpreted choices give every ordered pair probability one quarter.
example (i j : Fin 2) :
    ((binaryPMF id).bind fun a => (binaryPMF id).map fun b => (a, b)) (i, j) =
      (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
  simp [binaryPMF, PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    Prod.mk.injEq, ite_and, mul_ite]

-- Multiset interpretations may have more than two alternatives, with coincident endpoints.
private def threeChoices : Controller Multiset Unit ℕ ℕ where
  q₀ := 0
  halt q := q != 0
  transition _ _ := ↑[1, 1, 2]

private instance : Controller.HasState ℕ ℕ where
  state := id

private instance : Controller.Observe ℕ Unit where
  observe _ := ()

private instance : Controller.Apply ℕ ℕ where
  apply a _ := a

-- Halting freezes the three paths without collapsing their repeated endpoint.
example (n : ℕ) (hn : 1 ≤ n) :
    threeChoices.runFromWith (Interpretation.id Multiset) 0 n = ↑[1, 1, 2] := by
  apply threeChoices.runFromWith_eq_of_forall_halted (Interpretation.id Multiset) 0
    (n := 1) (hn := hn)
  intro d hd
  change d ∈ (↑[1, 1, 2] : Multiset ℕ) at hd
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

example {cs : List ℕ} {n : ℕ}
    (h : cs ∈ threeChoices.runTraceWith (Interpretation.id Multiset) 0 n) :
    cs.length = n + 1 :=
  threeChoices.length_of_mem_runTraceWith (Interpretation.id Multiset) 0 h
