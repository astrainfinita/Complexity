/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller

/-! # Finite action histories

A history records an initial configuration and a list of actions. Configurations are derived
by applying those actions; which controller can produce the history is a separate property.
-/

@[expose] public section

namespace Complexity.Controller

/-- An initial configuration and the actions of a finite execution segment. -/
@[ext]
structure History (Config Action : Type*) where
  /-- Initial configuration. -/
  first : Config
  /-- Recorded actions, in execution order. -/
  actions : List Action

namespace History

variable {Config Action Config' Action' : Type*}

/-- Number of recorded actions. -/
def length (p : History Config Action) : ℕ := p.actions.length

/-- A history with no actions. -/
@[simps actions]
def nil (c : Config) : History Config Action := ⟨c, []⟩

@[simp] theorem nil_length (c : Config) : (nil (Action := Action) c).length = 0 := rfl

/-- Append one action at the last configuration. -/
@[simps actions]
def snoc (p : History Config Action) (a : Action) : History Config Action :=
  ⟨p.first, p.actions ++ [a]⟩

@[simp] theorem snoc_length (p : History Config Action) (a : Action) :
    (p.snoc a).length = p.length + 1 := by simp [length]

variable [Apply Config Action] [Apply Config' Action']

/-- All configurations, including both endpoints, reconstructed in a single traversal. -/
def configs (p : History Config Action) : List Config :=
  p.actions.scanl (fun c a ↦ apply a c) p.first

/-- Final configuration. -/
def last (p : History Config Action) : Config :=
  p.actions.foldl (fun c a ↦ apply a c) p.first

@[simp] theorem length_configs (p : History Config Action) : p.configs.length = p.length + 1 :=
  List.length_scanl

theorem configs_ne_nil (p : History Config Action) : p.configs ≠ [] := List.scanl_ne_nil

@[simp] theorem head_configs (p : History Config Action) :
    p.configs.head p.configs_ne_nil = p.first := List.head_scanl _

theorem first_mem_configs (p : History Config Action) : p.first ∈ p.configs := by
  simpa using List.head_mem p.configs_ne_nil

theorem last_mem_configs (p : History Config Action) : p.last ∈ p.configs := by
  simpa only [configs, last, List.getLast_scanl] using List.getLast_mem p.configs_ne_nil

omit [Apply Config Action] in
@[simp] theorem first_nil (c : Config) : (nil (Action := Action) c).first = c := rfl

@[simp] theorem last_nil (c : Config) : (nil (Action := Action) c).last = c := rfl

@[simp] theorem configs_nil (c : Config) :
    (nil (Action := Action) c).configs = [c] := by simp [configs]

/-- Prepend an action whose successor is the first configuration of the remaining history. -/
@[simps actions]
def cons (c : Config) (a : Action) (tail : History Config Action)
    (_h : tail.first = apply a c) : History Config Action := ⟨c, a :: tail.actions⟩

@[simp] theorem cons_length (c : Config) (a : Action) (tail : History Config Action)
    (h : tail.first = apply a c) : (cons c a tail h).length = tail.length + 1 := rfl

@[simp] theorem first_cons (c : Config) (a : Action) (tail : History Config Action)
    (h : tail.first = apply a c) : (cons c a tail h).first = c := rfl

@[simp] theorem last_cons (c : Config) (a : Action) (tail : History Config Action)
    (h : tail.first = apply a c) : (cons c a tail h).last = tail.last := by
  simp [last, ← h]

@[simp] theorem configs_cons (c : Config) (a : Action) (tail : History Config Action)
    (h : tail.first = apply a c) : (cons c a tail h).configs = c :: tail.configs := by
  simp [configs, ← h]

/-- Map the initial configuration and recorded actions. -/
@[simps actions]
def map (p : History Config Action) (f : Config → Config') (g : Action → Action') :
    History Config' Action' :=
  ⟨f p.first, p.actions.map g⟩

omit [Apply Config Action] [Apply Config' Action'] in
@[simp] theorem map_length (p : History Config Action) (f : Config → Config')
    (g : Action → Action') : (p.map f g).length = p.length := by simp [length]

omit [Apply Config Action] [Apply Config' Action'] in
@[simp] theorem first_map (p : History Config Action) (f : Config → Config')
    (g : Action → Action') : (p.map f g).first = f p.first := rfl

@[simp] theorem last_map (p : History Config Action) (f : Config → Config')
    (g : Action → Action') (h : ∀ a c, f (apply a c) = apply (g a) (f c)) :
    (p.map f g).last = f p.last := by
  simp only [map, last, List.foldl_map]
  exact List.foldl_hom f (fun c a ↦ (h a c).symm)

@[simp] theorem configs_map (p : History Config Action) (f : Config → Config')
    (g : Action → Action') (h : ∀ a c, f (apply a c) = apply (g a) (f c)) :
    (p.map f g).configs = p.configs.map f := by
  rcases p with ⟨c, as⟩
  change (as.map g).scanl _ (f c) = (as.scanl _ c).map f
  induction as generalizing c with
  | nil => simp
  | cons a as ih => simp [← h, ih]

omit [Apply Config Action] [Apply Config' Action'] in
@[simp] theorem map_nil (c : Config) (f : Config → Config') (g : Action → Action') :
    (nil c).map f g = nil (f c) := rfl

omit [Apply Config Action] in
@[simp] theorem map_id (p : History Config Action) : p.map id id = p := by
  cases p; simp [map]

omit [Apply Config Action] [Apply Config' Action'] in
@[simp] theorem map_map (p : History Config Action) (f : Config → Config')
    (g : Action → Action') {Config'' Action'' : Type*}
    (f' : Config' → Config'') (g' : Action' → Action'') :
    (p.map f g).map f' g' = p.map (f' ∘ f) (g' ∘ g) := by simp [map, List.map_map]

/-- Join histories at their common configuration, recording it only once. -/
@[simps actions]
def append (p q : History Config Action) (_h : p.last = q.first) : History Config Action :=
  ⟨p.first, p.actions ++ q.actions⟩

@[simp] theorem append_length (p q : History Config Action) (h : p.last = q.first) :
    (p.append q h).length = p.length + q.length := by simp [length]

@[simp] theorem first_append (p q : History Config Action) (h : p.last = q.first) :
    (p.append q h).first = p.first := rfl

@[simp] theorem last_append (p q : History Config Action) (h : p.last = q.first) :
    (p.append q h).last = q.last := by
  simpa only [append, last, List.foldl_append] using congrArg (q.actions.foldl _) h

@[simp] theorem configs_append (p q : History Config Action) (h : p.last = q.first) :
    (p.append q h).configs = p.configs ++ q.configs.tail := by
  simp only [configs, append, List.scanl_append, ← h, last]

@[simp↓] theorem mem_configs_append (p q : History Config Action) (h : p.last = q.first)
    (c : Config) : c ∈ (p.append q h).configs ↔ c ∈ p.configs ∨ c ∈ q.configs := by
  rw [configs_append, List.mem_append, ← List.cons_head_tail q.configs_ne_nil]
  simp only [List.tail_cons, List.mem_cons, head_configs]
  have hp : q.first ∈ p.configs := h ▸ p.last_mem_configs
  aesop

@[simp] theorem nil_append (c : Config) (p : History Config Action) (h : p.first = c) :
    (nil c).append p h.symm = p := by cases p; simpa [append] using h.symm

@[simp] theorem append_nil (p : History Config Action) (c : Config) (h : p.last = c) :
    p.append (nil c) h = p := by cases p; simp [append]

@[simp] theorem cons_append (c : Config) (a : Action) (p q : History Config Action)
    (hp : p.first = apply a c) (hpq : p.last = q.first) :
    (cons c a p hp).append q (by simpa using hpq) =
      cons c a (p.append q hpq) (by simpa using hp) := rfl

/-- Regrouping connected segments leaves the complete history unchanged. -/
theorem append_assoc (p q r : History Config Action)
    (hpq : p.last = q.first) (hqr : q.last = r.first) :
    (p.append q hpq).append r (by simpa using hqr) =
      p.append (q.append r hqr) (by simpa using hpq) := by simp [append, List.append_assoc]

omit [Apply Config Action] in
@[simp] theorem first_snoc (p : History Config Action) (a : Action) :
    (p.snoc a).first = p.first := rfl

@[simp] theorem last_snoc (p : History Config Action) (a : Action) :
    (p.snoc a).last = apply a p.last := by simp [last]

@[simp] theorem configs_snoc (p : History Config Action) (a : Action) :
    (p.snoc a).configs = p.configs ++ [apply a p.last] := by
  simp [configs, List.scanl_append, last]

theorem snoc_append (p q : History Config Action) (a : Action)
    (h : q.first = apply a p.last) :
    (p.snoc a).append q (by simpa only [last_snoc] using h.symm) =
      p.append (cons p.last a q h) (by simp only [first_cons]) := by
  simp [append, List.append_assoc]

omit [Apply Config Action] [Apply Config' Action'] in
@[simp] theorem map_snoc (p : History Config Action) (a : Action)
    (f : Config → Config') (g : Action → Action') :
    (p.snoc a).map f g = (p.map f g).snoc (g a) := by simp [map, snoc]

@[simps]
instance {Q : Type*} [HasState Config Q] : HasState (History Config Action) Q where
  state p := state p.last

@[simps]
instance {Observation : Type*} [Observe Config Observation] :
    Observe (History Config Action) Observation where
  observe p := observe p.last

@[simps]
instance : Apply (History Config Action) Action where
  apply a p := p.snoc a

@[simp↓] theorem apply_last (a : Action) (p : History Config Action) :
    (apply a p).last = apply a p.last := last_snoc _ _

end History
end Complexity.Controller
