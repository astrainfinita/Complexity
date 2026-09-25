/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Resources.Basic

open Complexity

namespace Complexity.ResourcesTest

local instance : Encoding (Bool × ℕ) Bool where
  decode r := Part.some r.1
  exists_code b := ⟨(b, 0), Part.mem_some b⟩

-- The output can choose another code; the budget uses the actual input code.
example : Computes
    (fun (r q : Bool × ℕ) t s => q = (r.1, r.2 + 1) ∧ t = r.2 ∧ s = 0)
    Prod.snd (id : Bool → Bool) id (fun _ => 0) := by
  intro r a ha
  change a ∈ Part.some r.1 at ha
  obtain rfl := Part.mem_some_iff.mp ha
  exact ⟨(r.1, r.2 + 1), Part.mem_some r.1, rfl, rfl, rfl⟩

-- Handling just one selected code for each value is insufficient.
example : ¬ Computes
    (fun (r _ : Bool × ℕ) _ _ => r.2 = 0)
    Prod.snd (id : Bool → Bool) id id := by
  intro h
  obtain ⟨_, _, hr⟩ := h (false, 1) false (Part.mem_some false)
  cases hr

section Promise

variable (p : Bool → Prop)

local instance : Encoding (Bool × ℕ) {b // p b} where
  decode r := ⟨p r.1, fun h => ⟨r.1, h⟩⟩
  exists_code b := ⟨(b.val, 0), b.property, rfl⟩

-- The relation has no runs on invalid inputs. No decision procedure for p is needed.
example : Computes
    (fun (r q : Bool × ℕ) t s => p r.1 ∧ q.1 = r.1 ∧ t = r.2 ∧ s = 0)
    Prod.snd (Subtype.val : {b // p b} → Bool) id (fun _ => 0) := by
  intro r a ha
  obtain ⟨h, rfl⟩ := ha
  exact ⟨r, Part.mem_some r.1, h, rfl, rfl, rfl⟩

end Promise

end Complexity.ResourcesTest
