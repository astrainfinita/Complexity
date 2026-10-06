/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Compiler
public import Complexity.Resources.TreeMachine.Basic

/-! # Source program contracts as complexity witnesses -/

@[expose] public section

namespace Complexity.TreeProgram.Code

/-- A uniform source proof for an ordinary Lean function supplies one finite machine for all
inputs. The public complexity interface hides the generated control graph and register layout. -/
theorem computableInTimeAndSpace {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] (p : Code Value) (f : α → β)
    (time space : ℕ → ℕ)
    (h : ∀ a, p.Bounded 1 (Function.update (fun _ ↦ Tree.nil) 0 (encode Tree a))
      (time (encode Tree a).size) (space (encode Tree a).size)
      (fun v s ↦ v.eval s = encode Tree (f a)))
    (hx : ∀ a : α, (encode Tree a).size ≤ space (encode Tree a).size) :
    TimeSpaceModel.tree.ComputableInTimeAndSpace f (fun n ↦ time n + 4)
      (fun n ↦ p.registers * (space n + 2)) := by
  refine ⟨_, ⟨p.registers, inferInstance, _, inferInstance, p.compile, rfl⟩, ?_⟩
  exact Encoding.Computes.iff_of_uniqueEncoding.mpr fun a ↦ (h a).compile (hx a)

end Complexity.TreeProgram.Code
