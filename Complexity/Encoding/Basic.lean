/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Part

/-!
# Encodings and unique encodings

`Encoding R α` interprets raw data of type `R` as partial values of `α`. Every
value has a code, but different codes may denote the same value. The domain of
`decode` need not be decidable: this is a semantic interpretation, not an
algorithm whose execution is free.

`UniqueEncoding R α` additionally provides the unique code of each value. Its inverse
law applies to every valid code, not just the codes produced by `encode`.

Algorithm specifications should quantify over all valid input codes. These
classes impose no requirements on an algorithm's behavior on invalid inputs.
The raw type is explicit so the same value type can have both tree and bit-list
encodings. Alternative encodings on the same raw type can use local instances.

Concrete encoding functions use `R.encodeA` / `R.decodeA`: the namespace names
the code carrier and the suffix names the semantic data type. For example,
`BitList.encodeTree : Tree → List Bool` and `Tree.encodeBitList : List Bool → Tree`.
`BitList` is only a namespace for the `List Bool` carrier. Complete decoders use
`decodeA`; prefix parsers that also return an unconsumed suffix use `parseA`.

The generic operations expose the type not determined by their input:
`encode R a` specifies the code carrier, while `decode α r` specifies the
semantic data type. The other type is inferred from the supplied value.
-/

@[expose] public section

namespace Complexity

/-- A partial interpretation of raw data, covering every value. Valid codes
need not be unique, and validity need not be decidable. -/
class Encoding (R : Type*) (α : Type*) where
  /-- The value denoted by a raw code, when it is valid. -/
  decode (α) : R → Part α
  /-- Every value has at least one valid code. -/
  exists_code : ∀ a, ∃ r, a ∈ decode r

/-- An encoding in which every value has exactly one valid code. Invalid raw
data are still permitted. -/
class UniqueEncoding (R : Type*) (α : Type*) extends Encoding R α where
  /-- The unique code of a value. -/
  encode (R) : α → R
  /-- A code denotes a value exactly when it is that value's encoding. -/
  mem_decode_iff : ∀ {a r}, a ∈ decode r ↔ encode a = r
  exists_code a := ⟨encode a, mem_decode_iff.2 rfl⟩

export Encoding (decode)
export UniqueEncoding (encode)

namespace Encoding

variable {R : Type*} {α : Type*} {β : Type*}

@[ext] theorem ext {d e : Encoding R α} (h : ∀ r, d.decode r = e.decode r) : d = e := by
  cases d
  cases e
  congr
  exact funext h

/-- Interpret decoded values through a surjection. In particular, this supports
quotient values without choosing canonical representatives. -/
@[instance_reducible]
def map (d : Encoding R α) (f : α → β) (h : Function.Surjective f) : Encoding R β where
  decode r := (d.decode r).map f
  exists_code b := by
    obtain ⟨a, rfl⟩ := h b
    obtain ⟨r, hr⟩ := d.exists_code a
    exact ⟨r, Part.mem_map f hr⟩

@[simp] theorem mem_map_iff (d : Encoding R α) (f : α → β) (h : Function.Surjective f)
    {r : R} {b : β} : b ∈ (d.map f h).decode r ↔ ∃ a ∈ d.decode r, f a = b :=
  Part.mem_map_iff f

/-- Transport the value type of an encoding along an equivalence. This changes
the interpretation of codes; it makes no assertion about conversion costs. -/
@[instance_reducible]
def ofEquiv (d : Encoding R α) (e : β ≃ α) : Encoding R β :=
  d.map e.symm e.symm.surjective

@[simp high] theorem mem_ofEquiv_iff (d : Encoding R α) (e : β ≃ α) {r : R} {b : β} :
    b ∈ (d.ofEquiv e).decode r ↔ e b ∈ d.decode r := by
  simp [mem_map_iff, Equiv.symm_apply_eq]

/-- Restrict to values satisfying a predicate, without requiring a decision
procedure for that predicate. -/
@[instance_reducible]
def subtype (d : Encoding R α) (p : α → Prop) : Encoding R {a // p a} where
  decode r := (d.decode r).bind fun a => ⟨p a, fun h => ⟨a, h⟩⟩
  exists_code a := by
    obtain ⟨r, hr⟩ := d.exists_code a.val
    exact ⟨r, Part.mem_bind hr ⟨a.property, rfl⟩⟩

@[simp] theorem mem_subtype_iff (d : Encoding R α) (p : α → Prop)
    {r : R} {a : {a // p a}} : a ∈ (d.subtype p).decode r ↔ a.val ∈ d.decode r := by
  change a ∈ (d.decode r).bind (fun b => ⟨p b, fun h => ⟨b, h⟩⟩) ↔ _
  simp [Part.mem_bind_iff, Subtype.ext_iff, a.property]

end Encoding

namespace UniqueEncoding

variable {R : Type*} {α : Type*} {β : Type*}

/-- Construct a unique encoding from its two-sided partial inverse law. -/
@[instance_reducible]
def ofDecode (f : α → R) (g : R → Part α)
    (h : ∀ a r, a ∈ g r ↔ f a = r) : UniqueEncoding R α where
  decode := g
  encode := f
  mem_decode_iff := h _ _

/-- An executable partial decoder also gives a semantic unique encoding. -/
@[instance_reducible]
def ofOption (f : α → R) (g : R → Option α)
    (h : ∀ a r, g r = some a ↔ f a = r) : UniqueEncoding R α :=
  ofDecode f (fun r => Part.ofOption (g r)) fun a r => by
    simpa only [Part.mem_coe, Option.mem_def] using h a r

section

variable [UniqueEncoding R α]

@[simp] theorem decode_encode (a : α) : decode α (encode R a) = Part.some a :=
  Part.eq_some_iff.2 (mem_decode_iff.2 rfl)

theorem encode_of_mem_decode {a : α} {r : R} (h : a ∈ decode α r) : encode R a = r :=
  mem_decode_iff.1 h

@[simp] theorem decode_eq_some_iff {a : α} {r : R} :
    decode α r = Part.some a ↔ encode R a = r :=
  Part.eq_some_iff.trans mem_decode_iff

theorem encode_injective : Function.Injective (encode R (α := α)) := by
  intro a b h
  have := congrArg (decode α) h
  simpa using this

@[simp] theorem encode_inj {a b : α} : encode R a = encode R b ↔ a = b :=
  encode_injective.eq_iff

/-- Valid codes are precisely the image of the encoder. -/
theorem dom_decode_iff {r : R} : (decode α r).Dom ↔ ∃ a : α, encode R a = r := by
  simp only [Part.dom_iff_mem, mem_decode_iff]

end

/-- Use raw values as their own codes. This is an explicit choice of encoding,
so it does not silently override another interpretation of the same raw type. -/
@[instance_reducible]
def refl (R : Type*) : UniqueEncoding R R where
  decode := Part.some
  encode := id
  mem_decode_iff := Part.mem_some_iff

/-- Transport a unique encoding along an equivalence of value types. -/
@[instance_reducible]
def ofEquiv (c : UniqueEncoding R α) (e : β ≃ α) : UniqueEncoding R β where
  toEncoding := c.toEncoding.ofEquiv e
  encode b := c.encode (e b)
  mem_decode_iff := Encoding.mem_ofEquiv_iff c.toEncoding e |>.trans c.mem_decode_iff

@[simp] theorem ofEquiv_encode (c : UniqueEncoding R α) (e : β ≃ α) (b : β) :
    (c.ofEquiv e).encode b = c.encode (e b) := rfl

/-- Restrict a unique encoding to a subtype, retaining the underlying codes. -/
@[instance_reducible]
def subtype (c : UniqueEncoding R α) (p : α → Prop) : UniqueEncoding R {a // p a} where
  toEncoding := c.toEncoding.subtype p
  encode a := c.encode a.val
  mem_decode_iff := Encoding.mem_subtype_iff c.toEncoding p |>.trans c.mem_decode_iff

@[simp] theorem subtype_encode (c : UniqueEncoding R α) (p : α → Prop) (a : {a // p a}) :
    (c.subtype p).encode a = c.encode a.val := rfl

end UniqueEncoding

end Complexity
