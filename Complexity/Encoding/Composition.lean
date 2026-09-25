/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic

/-!
# Composition of encodings

`Encoding.comp e d` decodes raw data with `e`, then decodes the result with `d`.
When both encodings are unique, `UniqueEncoding.comp e d` encodes in the reverse
order. These are explicit constructions, not globally selected instances.
-/

@[expose] public section

namespace Complexity

namespace Encoding

variable {R : Type*} {S : Type*} {T : Type*} {α : Type*}

/-- Compose partial interpretations of codes. -/
@[instance_reducible]
def comp (e : Encoding R S) (d : Encoding S α) : Encoding R α where
  decode r := (e.decode r).bind d.decode
  exists_code a := by
    obtain ⟨s, hs⟩ := d.exists_code a
    obtain ⟨r, hr⟩ := e.exists_code s
    exact ⟨r, Part.mem_bind hr hs⟩

@[simp] theorem mem_comp_iff (e : Encoding R S) (d : Encoding S α) {r : R} {a : α} :
    a ∈ (e.comp d).decode r ↔ ∃ s ∈ e.decode r, a ∈ d.decode s :=
  Part.mem_bind_iff

theorem mem_comp_encode (e : UniqueEncoding R S) (d : Encoding S α)
    {s : S} {a : α} :
    a ∈ (e.toEncoding.comp d).decode (e.encode s) ↔ a ∈ d.decode s := by
  let := e
  change a ∈ (e.decode (e.encode s)).bind d.decode ↔ _
  simp

theorem comp_assoc (e : Encoding R S) (d : Encoding S T) (c : Encoding T α) :
    (e.comp d).comp c = e.comp (d.comp c) := by
  apply Encoding.ext
  intro r
  exact Part.bind_assoc _ _ _

@[simp] theorem refl_comp (e : Encoding R α) :
    (UniqueEncoding.refl R).toEncoding.comp e = e := by
  apply Encoding.ext
  intro r
  exact Part.bind_some _ _

@[simp] theorem comp_refl (e : Encoding R α) :
    e.comp (UniqueEncoding.refl α).toEncoding = e := by
  apply Encoding.ext
  intro r
  exact Part.bind_some_right _

end Encoding

namespace UniqueEncoding

variable {R : Type*} {S : Type*} {α : Type*}

/-- Compose unique encodings, encoding the value through the intermediate type. -/
@[instance_reducible]
def comp (e : UniqueEncoding R S) (d : UniqueEncoding S α) : UniqueEncoding R α where
  toEncoding := e.toEncoding.comp d.toEncoding
  encode a := e.encode (d.encode a)
  mem_decode_iff := by
    intro a r
    rw [Encoding.mem_comp_iff]
    constructor
    · rintro ⟨s, hs, ha⟩
      exact (congrArg e.encode (d.mem_decode_iff.1 ha)).trans (e.mem_decode_iff.1 hs)
    · intro h
      exact ⟨d.encode a, e.mem_decode_iff.2 h, d.mem_decode_iff.2 rfl⟩

@[simp] theorem comp_encode (e : UniqueEncoding R S) (d : UniqueEncoding S α) (a : α) :
    (e.comp d).encode a = e.encode (d.encode a) := rfl

end UniqueEncoding

end Complexity
