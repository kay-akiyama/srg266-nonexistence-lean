/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7Residual

/-!
# Bit coordinates for the special `4 × 8` Clebsch check

The sixteen first-factor weights are represented by an explicit bijection.
The checked predicate uses Boolean characteristic functions and finite sums;
separate lemmas transport the result back to arbitrary `Finset`s.
-/

namespace SRG266
namespace E7FourEightSpecialCrossData

set_option maxRecDepth 100000

def d₄ : Fin 8 → ℤ :=
  ![-3, -1, -1, 1, 1, 1, 1, 1]

abbrev FirstWeight :=
  {w : E7WeightIndex // e7ResidualEvaluation d₄ w = 1}

instance : Fintype FirstWeight :=
  Fintype.subtype
    (Finset.univ.filter fun w => e7ResidualEvaluation d₄ w = 1)
    (by simp)

def crossAllowed (s : Finset FirstWeight) : Finset FirstWeight :=
  Finset.univ.filter fun b =>
    ∀ a ∈ s, 0 ≤ e7WeightPairing2 a.1 b.1

def firstWeight : Fin 16 → FirstWeight := ![
  ⟨(false, ⟨18, by decide⟩), by decide⟩,
  ⟨(false, ⟨19, by decide⟩), by decide⟩,
  ⟨(false, ⟨20, by decide⟩), by decide⟩,
  ⟨(false, ⟨21, by decide⟩), by decide⟩,
  ⟨(false, ⟨22, by decide⟩), by decide⟩,
  ⟨(false, ⟨23, by decide⟩), by decide⟩,
  ⟨(false, ⟨24, by decide⟩), by decide⟩,
  ⟨(false, ⟨25, by decide⟩), by decide⟩,
  ⟨(false, ⟨26, by decide⟩), by decide⟩,
  ⟨(false, ⟨27, by decide⟩), by decide⟩,
  ⟨(true, ⟨2, by decide⟩), by decide⟩,
  ⟨(true, ⟨3, by decide⟩), by decide⟩,
  ⟨(true, ⟨4, by decide⟩), by decide⟩,
  ⟨(true, ⟨5, by decide⟩), by decide⟩,
  ⟨(true, ⟨6, by decide⟩), by decide⟩,
  ⟨(true, ⟨7, by decide⟩), by decide⟩
]

/-- Literal nonnegative-pairing table on the sixteen Clebsch vertices. -/
def compatible : Fin 16 → Fin 16 → Bool := ![
  ![true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true],
  ![true, true, true, true, true, false, false, true, true, false, false, true, false, true, true, true],
  ![true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true],
  ![true, true, true, true, false, false, true, false, true, true, false, true, true, true, false, true],
  ![true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true],
  ![true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, true],
  ![true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true],
  ![false, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true],
  ![false, true, false, true, true, false, true, true, true, true, true, true, false, true, false, true],
  ![false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true],
  ![false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, false],
  ![false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false],
  ![true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false],
  ![true, true, false, true, true, false, true, false, true, false, true, true, true, true, true, false],
  ![true, true, true, false, true, true, false, true, false, false, true, true, true, true, true, false],
  ![true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true]
]

theorem compatible_iff_nonnegative (i j : Fin 16) :
    compatible i j = true ↔
      0 ≤ e7WeightPairing2 (firstWeight i).1 (firstWeight j).1 := by
  decide +kernel +revert

abbrev ShellBits := Fin 16 → Bool

def selectedCount (bits : ShellBits) : ℕ :=
  ∑ i, if bits i = true then 1 else 0

def allowedAt (bits : ShellBits) (j : Fin 16) : Prop :=
  ∀ i, bits i = true →
    compatible i j = true

instance (bits : ShellBits) : DecidablePred (allowedAt bits) :=
  fun _ => by unfold allowedAt; infer_instance

def allowedCount (bits : ShellBits) : ℕ :=
  ∑ j, if allowedAt bits j then 1 else 0

def characteristic (s : Finset FirstWeight) : ShellBits :=
  fun i => decide (firstWeight i ∈ s)

end E7FourEightSpecialCrossData
end SRG266
