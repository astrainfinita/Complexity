/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Wiring and composing circuits

Input relabeling permits permutations, duplication, and restriction to selected inputs. Sequential
composition retains each gate once, even when several downstream inputs use the same output.
All constructions preserve the explicit gate count and work for zero inputs or outputs.
-/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {M : Type w} {n m k p : ℕ}

/-- Extend a wire substitution across a newly computed gate. -/
def liftInputs (f : Fin n → Fin k) : Fin (n + 1) → Fin (k + 1) :=
  Fin.snoc (Fin.castSucc ∘ f) (Fin.last k)

@[simp] theorem liftInputs_castSucc (f : Fin n → Fin k) (i : Fin n) :
    liftInputs f i.castSucc = (f i).castSucc := by simp [liftInputs]

@[simp] theorem liftInputs_last (f : Fin n → Fin k) :
    liftInputs f (Fin.last n) = Fin.last k := by simp [liftInputs]

@[simp] theorem snoc_comp_liftInputs (f : Fin n → Fin k) (x : Fin k → M) (y : M) :
    Fin.snoc x y ∘ liftInputs f = Fin.snoc (x ∘ f) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem liftInputs_id : liftInputs (_root_.id : Fin n → Fin n) = _root_.id := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem liftInputs_comp (f : Fin n → Fin k) (g : Fin k → Fin p) :
    liftInputs (g ∘ f) = liftInputs g ∘ liftInputs f := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Substitute available input wires without copying any gate. -/
def relabel : {n m k : ℕ} → Circuit L n m → (Fin n → Fin k) → Circuit L k m
  | _, _, _, .outputs select, f => .outputs (f ∘ select)
  | _, _, _, .gate op args next, f =>
      .gate op (f ∘ args) (next.relabel (liftInputs f))

@[simp] theorem relabel_id (c : Circuit L n m) : c.relabel _root_.id = c := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [relabel, ih]

@[simp] theorem relabel_relabel (c : Circuit L n m) (f : Fin n → Fin k)
    (g : Fin k → Fin p) : (c.relabel f).relabel g = c.relabel (g ∘ f) := by
  induction c generalizing k p with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [relabel, ih, liftInputs_comp, Function.comp_assoc]

@[simp] theorem size_relabel (c : Circuit L n m) (f : Fin n → Fin k) :
    (c.relabel f).size = c.size := by
  induction c generalizing k with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [relabel, ih]

@[simp] theorem evalWith_relabel (c : Circuit L n m) (f : Fin n → Fin k)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin k → M) :
    (c.relabel f).evalWith ops x = c.evalWith ops (x ∘ f) := by
  induction c generalizing k with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [relabel, ih, Function.comp_assoc]

@[simp] theorem eval_relabel [L.Structure M] (c : Circuit L n m)
    (f : Fin n → Fin k) (x : Fin k → M) :
    (c.relabel f).eval x = c.eval (x ∘ f) := evalWith_relabel _ _ _ _

/-- Run `c`, then feed its outputs to `d`. Shared outputs remain shared wires. -/
def comp : {n m : ℕ} → Circuit L n m → Circuit L m k → Circuit L n k
  | _, _, .outputs select, d => d.relabel select
  | _, _, .gate op args next, d => .gate op args (next.comp d)

@[simp] theorem size_comp (c : Circuit L n m) (d : Circuit L m k) :
    (c.comp d).size = c.size + d.size := by
  induction c with
  | outputs _ => simp [comp]
  | gate _ _ _ ih => simp [comp, ih, Nat.add_right_comm]

@[simp] theorem evalWith_comp (c : Circuit L n m) (d : Circuit L m k)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    (c.comp d).evalWith ops x = d.evalWith ops (c.evalWith ops x) := by
  induction c with
  | outputs _ => simp [comp]
  | gate _ _ _ ih => simp [comp, ih]

@[simp] theorem eval_comp [L.Structure M] (c : Circuit L n m)
    (d : Circuit L m k) (x : Fin n → M) :
    (c.comp d).eval x = d.eval (c.eval x) := evalWith_comp _ _ _ _

/-- Select, permute, or duplicate outputs, retaining the same stored gates. -/
def mapOutputs (c : Circuit L n m) (f : Fin k → Fin m) : Circuit L n k :=
  c.comp (outputs f)

@[simp] theorem size_mapOutputs (c : Circuit L n m) (f : Fin k → Fin m) :
    (c.mapOutputs f).size = c.size := by simp [mapOutputs]

@[simp] theorem evalWith_mapOutputs (c : Circuit L n m) (f : Fin k → Fin m)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    (c.mapOutputs f).evalWith ops x = c.evalWith ops x ∘ f := by simp [mapOutputs]

@[simp] theorem eval_mapOutputs [L.Structure M] (c : Circuit L n m)
    (f : Fin k → Fin m) (x : Fin n → M) :
    (c.mapOutputs f).eval x = c.eval x ∘ f := evalWith_mapOutputs _ _ _ _

@[simp] theorem id_comp (c : Circuit L n m) : (id L n).comp c = c := by
  simp [id, comp]

@[simp] theorem comp_id (c : Circuit L n m) : c.comp (id L m) = c := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [comp, ih]

/-- Wiring a composite's inputs is the same as wiring its first component's inputs. -/
theorem relabel_comp (c : Circuit L n m) (d : Circuit L m k) (f : Fin n → Fin p) :
    (c.comp d).relabel f = (c.relabel f).comp d := by
  induction c generalizing p with
  | outputs _ => simp [comp, relabel]
  | gate _ _ _ ih => simp [comp, relabel, ih]

/-- Circuit composition is associative as syntax, retaining the same sequence of gates. -/
theorem comp_assoc (c : Circuit L n m) (d : Circuit L m k) (e : Circuit L k p) :
    (c.comp d).comp e = c.comp (d.comp e) := by
  induction c with
  | outputs _ => simp [comp, relabel_comp]
  | gate _ _ _ ih => simp [comp, ih]

/-- Specifications compose in the same order as circuits. -/
theorem Computes.comp [L.Structure M] {c : Circuit L n m} {d : Circuit L m k}
    {f : (Fin n → M) → Fin m → M} {g : (Fin m → M) → Fin k → M}
    (hc : c.Computes f) (hd : d.Computes g) : (c.comp d).Computes (g ∘ f) := by
  intro x
  simp [hc x, hd (f x)]

/-- Return the selected wires followed by the outputs, without adding gates. The selection is
carried past each gate and written once with the outputs. -/
def keepWires : {n m : ℕ} → Circuit L n m → (Fin p → Fin n) → Circuit L n (p + m)
  | _, _, .outputs select, keep => .outputs (Fin.append keep select)
  | _, _, .gate op args next, keep => .gate op args (next.keepWires (Fin.castSucc ∘ keep))

@[simp] theorem size_keepWires (c : Circuit L n m) (keep : Fin p → Fin n) :
    (c.keepWires keep).size = c.size := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [keepWires, ih]

@[simp] theorem evalWith_keepWires (c : Circuit L n m) (keep : Fin p → Fin n)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    (c.keepWires keep).evalWith ops x = Fin.append (x ∘ keep) (c.evalWith ops x) := by
  induction c with
  | outputs select =>
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [keepWires, Function.comp_def]
  | gate op args next ih =>
      simp only [keepWires, evalWith_gate, ih]
      congr 1
      funext j
      simp

@[simp] theorem eval_keepWires [L.Structure M] (c : Circuit L n m) (keep : Fin p → Fin n)
    (x : Fin n → M) : (c.keepWires keep).eval x = Fin.append (x ∘ keep) (c.eval x) :=
  evalWith_keepWires _ _ _ _

/-- Return the original inputs followed by the outputs, without adding gates. -/
def keepInputs (c : Circuit L n m) : Circuit L n (n + m) := c.keepWires _root_.id

@[simp] theorem size_keepInputs (c : Circuit L n m) : c.keepInputs.size = c.size :=
  size_keepWires _ _

@[simp] theorem evalWith_keepInputs (c : Circuit L n m)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    c.keepInputs.evalWith ops x = Fin.append x (c.evalWith ops x) :=
  evalWith_keepWires _ _ _ _

@[simp] theorem eval_keepInputs [L.Structure M] (c : Circuit L n m) (x : Fin n → M) :
    c.keepInputs.eval x = Fin.append x (c.eval x) := evalWith_keepInputs _ _ _

/-- Evaluate two circuits on the same inputs and concatenate their outputs. Each circuit's
stored gates are included once. -/
def fanout (c : Circuit L n m) (d : Circuit L n k) : Circuit L n (m + k) :=
  (c.keepInputs.comp (d.relabel (Fin.castAdd m)).keepInputs).mapOutputs
    (Fin.append (fun i : Fin m => Fin.castAdd k (Fin.natAdd n i)) (Fin.natAdd (n + m)))

@[simp] theorem size_fanout (c : Circuit L n m) (d : Circuit L n k) :
    (c.fanout d).size = c.size + d.size := by simp [fanout]

@[simp] theorem evalWith_fanout (c : Circuit L n m) (d : Circuit L n k)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    (c.fanout d).evalWith ops x = Fin.append (c.evalWith ops x) (d.evalWith ops x) := by
  simp only [fanout, evalWith_mapOutputs, evalWith_comp, evalWith_keepInputs, evalWith_relabel]
  have hx : Fin.append x (c.evalWith ops x) ∘ Fin.castAdd m = x := by funext i; simp
  rw [hx]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

@[simp] theorem eval_fanout [L.Structure M] (c : Circuit L n m)
    (d : Circuit L n k) (x : Fin n → M) :
    (c.fanout d).eval x = Fin.append (c.eval x) (d.eval x) := evalWith_fanout _ _ _ _

/-- Combine a finite tuple of single-output circuits on the same input wires. -/
def bundle : {k : ℕ} → (Fin k → Circuit L n 1) → Circuit L n k
  | 0, _ => outputs Fin.elim0
  | k + 1, cs => (bundle fun i : Fin k => cs i.castSucc).fanout (cs (Fin.last k))

@[simp] theorem size_bundle (cs : Fin k → Circuit L n 1) :
    (bundle cs).size = ∑ i, (cs i).size := by
  induction k with
  | zero => simp [bundle]
  | succ k ih => simp [bundle, ih, Fin.sum_univ_castSucc]

@[simp] theorem evalWith_bundle (cs : Fin k → Circuit L n 1)
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M) (x : Fin n → M) :
    (bundle cs).evalWith ops x = fun i => (cs i).evalWith ops x 0 := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
      simp only [bundle, evalWith_fanout, ih, Fin.append_right_eq_snoc]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem eval_bundle [L.Structure M] (cs : Fin k → Circuit L n 1)
    (x : Fin n → M) : (bundle cs).eval x = fun i => (cs i).eval x 0 :=
  evalWith_bundle _ _ _

/-- Rename each operation to a symbol of the same arity. This performs no gate expansion. -/
def map (φ : L →ᴸ L') : {n m : ℕ} → Circuit L n m → Circuit L' n m
  | _, _, .outputs select => .outputs select
  | _, _, .gate op args next => .gate (φ.onFunction op) args (next.map φ)

@[simp] theorem size_map (c : Circuit L n m) (φ : L →ᴸ L') :
    (c.map φ).size = c.size := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [map, ih]

/-- Renaming symbols preserves evaluation when the interpretations agree on each symbol. -/
theorem evalWith_map (c : Circuit L n m) (φ : L →ᴸ L')
    (ops : ∀ {r}, L.Functions r → (Fin r → M) → M)
    (ops' : ∀ {r}, L'.Functions r → (Fin r → M) → M)
    (h : ∀ {r} (op : L.Functions r) x, ops' (φ.onFunction op) x = ops op x)
    (x : Fin n → M) : (c.map φ).evalWith ops' x = c.evalWith ops x := by
  induction c with
  | outputs _ => rfl
  | gate _ _ _ ih => simp [map, ih, h]

end Complexity.Circuit
