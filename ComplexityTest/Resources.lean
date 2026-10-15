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

-- The condition can use both the value and its actual code, with no resource convention.
example : Encoding.Computes (id : Bool → Bool)
    (fun b (src dst : Bool × ℕ) =>
      dst = (b, src.2 + 1)) := by
  intro a r ha
  change a ∈ Part.some r.1 at ha
  obtain rfl := Part.mem_some_iff.mp ha
  exact ⟨(r.1, r.2 + 1), Part.mem_some r.1, rfl⟩

-- Handling just one selected code for each value is insufficient.
example : ¬ Encoding.Computes (id : Bool → Bool)
    (fun _ (src _ : Bool × ℕ) => src.2 = 0) := by
  intro h
  obtain ⟨_, _, hr⟩ := h false (false, 1) (Part.mem_some false)
  cases hr

-- An output satisfying the condition must also encode the specified result.
-- There are correct outputs, and outputs whose first component is true, but no shared witness.
example : ¬ Encoding.Computes (fun _ : Bool => false)
    (fun _ (_ dst : Bool × ℕ) => dst.1 = true) := by
  intro h
  obtain ⟨q, hq, htrue⟩ := h false (false, 0) (Part.mem_some false)
  change false ∈ Part.some q.1 at hq
  have hfalse := Part.mem_some_iff.mp hq
  simp [← hfalse] at htrue

-- Weakening the condition preserves the very same correct output witness.
example {f : Bool → Bool} {P Q : Bool → (Bool × ℕ) → (Bool × ℕ) → Prop}
    (h : Encoding.Computes f P) (hPQ : ∀ a r q, P a r q → Q a r q) :
    Encoding.Computes f Q :=
  h.mono (fun hP => hPQ _ _ _ hP)

section Promise

variable (p : Bool → Prop)

local instance : Encoding (Bool × ℕ) {b // p b} where
  decode r := ⟨p r.1, fun h => ⟨r.1, h⟩⟩
  exists_code b := ⟨(b.val, 0), b.property, rfl⟩

-- The relation has no runs on invalid inputs. No decision procedure for p is needed.
example : Encoding.Computes (Subtype.val : {b // p b} → Bool)
    (fun _ (src dst : Bool × ℕ) =>
      p src.1 ∧ dst.1 = src.1) := by
  intro a r ha
  obtain ⟨h, rfl⟩ := ha
  exact ⟨r, Part.mem_some r.1, h, rfl⟩

end Promise

end Complexity.ResourcesTest
