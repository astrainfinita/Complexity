/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic

/-!
# Decision specifications

`Encoding.Computes` supplies the common encoded computation predicate.
Resource models specialize its condition to execution and budgets; this file
adds the Boolean correctness condition used by deterministic decision classes.
-/

@[expose] public section

namespace Complexity

variable {Data α β : Type*}

/-- A Boolean-valued function decides a predicate, including rejection of every
value outside the predicate. -/
def Decides (f : α → Bool) (p : α → Prop) : Prop :=
  ∀ a, f a = true ↔ p a

namespace Decides

theorem congr {f : α → Bool} {p q : α → Prop} (h : Decides f p)
    (hp : ∀ a, p a ↔ q a) : Decides f q :=
  fun a => (h a).trans (hp a)

theorem comp {f : α → β} {g : β → Bool} {q : β → Prop} (h : Decides g q) :
    Decides (g ∘ f) (q ∘ f) :=
  fun a => h (f a)

end Decides

end Complexity
