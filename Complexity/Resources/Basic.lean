/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic

/-!
# Resource bounds for functions on encoded values

`Computes run size f t s` lifts a raw computation relation to a function between
encoded types. It requires a terminating computation on every valid input code,
with bounds measured on that actual code. Any valid code for the result is allowed.
Invalid inputs impose no obligations, and decoding is not an extra machine operation.

The machine-specific layers supply `run` and `size`. They quantify over a single
finite machine before quantifying over input values and codes.
-/

@[expose] public section

namespace Complexity

variable {Data α β : Type*}

/-- A raw computation implements a function on every valid input representation,
within time and space bounds measured on that representation. -/
def Computes [Encoding Data α] [Encoding Data β]
    (run : Data → Data → ℕ → ℕ → Prop) (size : Data → ℕ) (f : α → β)
    (t s : ℕ → ℕ) : Prop :=
  ∀ r a, a ∈ decode α r → ∃ q, f a ∈ decode β q ∧ run r q (t (size r)) (s (size r))

namespace Computes

variable {run : Data → Data → ℕ → ℕ → Prop} {size : Data → ℕ} {f : α → β}
  {t s t' s' : ℕ → ℕ}

/-- Increasing either resource budget preserves a computation when the raw
computation relation permits the same increase. -/
theorem mono [Encoding Data α] [Encoding Data β] (h : Computes run size f t s)
    (hm : ∀ {r q t s t' s'}, run r q t s → t ≤ t' → s ≤ s' → run r q t' s')
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) : Computes run size f t' s' := by
  intro r a ha
  obtain ⟨q, hq, hr⟩ := h r a ha
  exact ⟨q, hq, hm hr (ht _) (hs _)⟩

/-- A unique output encoding removes the output witness without restricting input codes. -/
theorem iff_of_uniqueOutput [Encoding Data α] [UniqueEncoding Data β] :
    Computes run size f t s ↔
      ∀ r a, a ∈ decode α r →
        run r (encode Data (f a)) (t (size r)) (s (size r)) := by
  constructor
  · intro h r a ha
    obtain ⟨q, hq, hr⟩ := h r a ha
    rwa [← UniqueEncoding.encode_of_mem_decode hq] at hr
  · intro h r a ha
    exact ⟨encode Data (f a), UniqueEncoding.mem_decode_iff.2 rfl, h r a ha⟩

/-- For unique input and output encodings, the representation-based specification
reduces to computing the encoder's result on the encoder's input. -/
theorem iff_of_uniqueEncoding [UniqueEncoding Data α] [UniqueEncoding Data β] :
    Computes run size f t s ↔
      ∀ a, run (encode Data a) (encode Data (f a))
        (t (size (encode Data a))) (s (size (encode Data a))) := by
  rw [iff_of_uniqueOutput]
  constructor
  · intro h a
    exact h (encode Data a) a (UniqueEncoding.mem_decode_iff.2 rfl)
  · intro h r a ha
    obtain rfl := (UniqueEncoding.encode_of_mem_decode ha).symm
    exact h a

end Computes

/-- A Boolean-valued function decides a predicate, including rejection of every
value outside the predicate. -/
def Decides (f : α → Bool) (p : α → Prop) : Prop :=
  ∀ a, f a = true ↔ p a

namespace Decides

theorem congr {f : α → Bool} {p q : α → Prop} (h : Decides f p)
    (hp : ∀ a, p a ↔ q a) : Decides f q :=
  fun a => (h a).trans (hp a)

end Decides

end Complexity
