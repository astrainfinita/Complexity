/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.StackMachine.Basic
public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Models.StackMachine.Program.Correctness
public import Complexity.Encoding.Bool

/-!
# Nondeterministic decisions by choice programs

A stack program with choices of any shape `F`, read in `Multiset`, decides a predicate on
`TimeSpaceModel.stackWith F Multiset` when two specifications hold on every legal input code: under
`MonadQuant.all`, every run halts within the budget with the code of some Boolean, `true` only when
the predicate holds; under `MonadQuant.any`, when the predicate holds, some run halts within the
budget with the code of `true` (`StackMachine.Program.nDecidableWithinByCode_of_spec`). The machine
is the compiled program and the time is the budget. The instance arguments are those of the
correctness of compilation. With `F = BinaryChoice` the model is `TimeSpaceModel.nstack`.

The space bound is taken from the time bound, `Fintype.card κ * t`; an entry with a separate space
bound is not stated yet. This is the current state, not a decision.
-/

@[expose] public section

namespace Complexity.StackMachine.Program

open Std.WP

/-- A stack program with choices of shape `F` decides `p` on `TimeSpaceModel.stackWith F Multiset`
within the budget `t` when, on every legal input code, every run halts within `t` steps with the
code of some Boolean, `true` only when `p` holds (`MonadQuant.all`), and when `p` holds some run
halts within `t` steps with the code of `true` (`MonadQuant.any`). The answer is read from the
output, not from the result of the program, and the space is bounded by the time. -/
theorem nDecidableWithinByCode_of_spec {F : Type → Type} [Functor F] [Pure F]
    [MonadLiftT F Multiset] [LawfulFunctorLiftT F Multiset] [MonadQuant.PureLiftT F Multiset .all]
    [MonadQuant.PureLiftT F Multiset .any] {κ : Type} [Fintype κ] {α : Type*}
    [Encoding (RawWord Bool) α] {p : α → Prop} {β : Type}
    (prog : StackMachine.Program F κ Bool β) (t : α → RawWord Bool → ℕ)
    (hall : ∀ a r, a ∈ decode α r →
      Triple (prog.verifyWith Multiset .all (semantics r.toList.toArray))
        (fun s b ↦ s = Cfg.init κ r.toList ∧ b = t a r)
        (fun _ s _ ↦ ∃ v : Bool, s.output = ⌜v⌝₂.toList.toArray ∧ (v = true → p a)) ())
    (hany : ∀ a r, a ∈ decode α r → p a →
      Triple (prog.verifyWith Multiset .any (semantics r.toList.toArray))
        (fun s b ↦ s = Cfg.init κ r.toList ∧ b = t a r)
        (fun _ s _ ↦ s.output = ⌜true⌝₂.toList.toArray) ()) :
    (TimeSpaceModel.stackWith F Multiset).NDecidableWithinByCode p t
      (fun a r ↦ Fintype.card κ * t a r) := by
  refine ⟨_, ⟨κ, inferInstance, _, inferInstance, compile prog, rfl⟩, ?_⟩
  rw [Encoding.NDecides.iff_of_uniqueOutput]
  intro a r ha
  -- The answer of a configuration: whether its output is the code of `true`.
  let ans (c : (prog.State ⊕ prog.Exit) × Cfg κ Bool r.toList.toArray) : Bool :=
    decide (c.2.output = (⌜true⌝₂ : RawWord Bool).toList.toArray)
  have hans : ∀ c ∈ returns ((compile prog).runWith Multiset r.toList (t a r)),
      (compile prog).Halted c ∧ c.2.output = (⌜ans c⌝₂ : RawWord Bool).toList.toArray ∧
        (ans c = true → p a) := by
    intro c hc
    obtain ⟨x, s, rfl, -, -, v, hv, hp⟩ :=
      (Program.execWithinWith_of_spec (hall a r ha) ⟨rfl, rfl⟩).runFromWith_compile eval idle c hc
    have : ans (.inr x, s) = v := by
      simp only [ans, hv, Array.mk.injEq, RawWord.toList_inj, UniqueEncoding.encode_inj,
        Bool.decide_eq_true]
    exact ⟨rfl, this ▸ hv, this ▸ hp⟩
  refine ⟨((compile prog).runWith Multiset r.toList (t a r)).map ans, ?_, fun hb ↦ ?_, fun hp ↦ ?_⟩
  · simpa only [Multiset.fmap_def, Multiset.map_map, Function.comp_def] using
      ComputesWithinWith.of_forall_halted (compile prog) r.toList
        (fun c ↦ (⌜ans c⌝₂ : RawWord Bool).toList) fun c hc ↦ ⟨(hans c hc).1, (hans c hc).2.1⟩
  · obtain ⟨c, hc, hcb⟩ := Multiset.mem_map.1 hb
    exact (hans c hc).2.2 hcb
  · obtain ⟨c, hc, x, s, rfl, -, -, hs⟩ :=
      (Program.execWithinWith_of_spec (hany a r ha hp) ⟨rfl, rfl⟩).runFromWith_compile eval idle
    exact Multiset.mem_map.2 ⟨_, hc, by simp only [ans, hs, decide_true]⟩

end Complexity.StackMachine.Program
