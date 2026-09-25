/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Asymptotics

open Complexity

-- An exceptional zero-length input need not satisfy the eventual comparison.
example : IsBigO (fun n => if n = 0 then 1000 else n) id :=
  IsBigO.iff_exists_nat.2 ⟨1, 1, fun n hn => by simp [show n ≠ 0 by omega]⟩

-- O(0) remains O(0); no hidden +1 admits positive constant resource use.
example : ¬IsBigO (fun _ => 1) (fun _ => 0) := by
  intro h
  obtain ⟨c, n, hn⟩ := IsBigO.iff_exists_nat.1 h
  simpa using hn n le_rfl
