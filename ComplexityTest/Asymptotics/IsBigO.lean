/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Asymptotics.IsBigO

open Complexity

-- The heavier comparison is available only when its bridge is imported.
example (f g : ℕ → ℕ) : DominatedAtTop f g ↔
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) :=
  dominatedAtTop_iff_isBigO_natCast
