/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.CorankFourStatement

/-!
# The rooted norm-one-free classification statement

This module transports `SRG266.RootedCorankFourClassification` through the
frame complement to the host-and-frame formulation used by the graph proof.
-/

namespace SRG266

/-! ## The host-and-frame statement -/

/-- A rank-15 odd unimodular host, after removing at most three orthonormal
norm-one directions, has one of the three coordinate core models relevant to
the graph embedding.

The norm-two and norm-three clauses are supplied by the graph and are not used
by the corank-four transport below. -/
abbrev RootedNormOneFreeClassification : Prop :=
  ∀ (L : OddUnimodularLattice15) (k : ℕ) (u : Fin k → L.carrier),
    k ≤ 3 →
    (∀ i, L.pairing (u i) (u i) = 1) →
    (∀ i j, i ≠ j → L.pairing (u i) (u j) = 0) →
    (∀ w : L.carrier, (∀ i, L.pairing (u i) w = 0) → L.pairing w w ≠ 1) →
    (∃ a : L.carrier, (∀ i, L.pairing (u i) a = 0) ∧ L.pairing a a = 2) →
    (∃ w : L.carrier, (∀ i, L.pairing (u i) w = 0) ∧ L.pairing w w = 3) →
      Lattice.IsHostCoreModel L u Lattice.d12PlusGram ∨
        Lattice.IsHostCoreModel L u Lattice.e7e7PlusGram ∨
        Lattice.IsHostCoreModel L u Lattice.a15PlusGram

/-- The corank-four classification supplies the rooted host-and-frame statement
by classifying the frame complement and transporting its matrix model back to
the host. -/
theorem rootedNormOneFreeClassification_of_corankFour
    (hCorank : RootedCorankFourClassification) :
    RootedNormOneFreeClassification := by
  intro L k u hk hnorm horth hfree _ _
  obtain ⟨L₀, ι, hpair, hcover, hnormOne⟩ :=
    L.exists_frameCore u hnorm horth hfree
  rcases hCorank (15 - k) (by omega) (by omega) L₀ hnormOne with
    hd12 | he7 | ha15
  · exact Or.inl
      (Lattice.isHostCoreModel_of_isMatrixModel ι hpair hcover hd12)
  · exact Or.inr (Or.inl
      (Lattice.isHostCoreModel_of_isMatrixModel ι hpair hcover he7))
  · exact Or.inr (Or.inr
      (Lattice.isHostCoreModel_of_isMatrixModel ι hpair hcover ha15))

end SRG266
