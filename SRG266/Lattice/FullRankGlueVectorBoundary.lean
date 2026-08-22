/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.A15GlueTransport
import SRG266.Lattice.D12GlueTransport
import SRG266.Lattice.E7E7GlueTransport
import SRG266.Lattice.ThetaEutaxyBoundary

/-!
# The full-rank glue-vector boundary

Each possible root type is reduced to the existence of one normalized glue
vector:

* `D12`: `2 x` is the standard spinor numerator;
* `E7 + E7`: `2 x` is the standard diagonal numerator;
* `A15`: `4 x` is the standard order-four numerator.

These statements are the exact endpoint of the remaining discriminant-group
argument.  They contain no coordinate-model conclusion, no shell
normalization, and no graph-specific enumeration.
-/

namespace SRG266

open scoped Matrix

/-- The residual `D12` glue statement: after normalizing one of the two spinor
classes, its standard numerator is divisible by two in the ambient lattice. -/
abbrev D12NormalizedGlueVectorInput : Prop :=
  ∀ (L : PDUnimodularLattice 12),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.D 12] →
      ∃ (f : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier),
        (∀ v w, L.pairing (f v) (f w) =
          Matrix.toBilin' (Lattice.gramD 12) v w) ∧
        (2 : ℤ) • x = f Lattice.d12GlueNumerator

/-- The residual `E7 + E7` glue statement: the standard diagonal numerator is
divisible by two in the ambient lattice. -/
abbrev E7E7NormalizedGlueVectorInput : Prop :=
  ∀ (L : PDUnimodularLattice 14),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.E7, .E7] →
      ∃ (f : (Fin 14 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier),
        (∀ v w, L.pairing (f v) (f w) =
          Matrix.toBilin' (Lattice.adeGram [.E7, .E7]).2 v w) ∧
        (2 : ℤ) • x = f Lattice.e7e7GlueNumerator

/-- The residual `A15` glue statement: the standard order-four numerator is
divisible by four in the ambient lattice. -/
abbrev A15NormalizedGlueVectorInput : Prop :=
  ∀ (L : PDUnimodularLattice 15),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.A 15] →
      ∃ (f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier),
        (∀ v w, L.pairing (f v) (f w) =
          Matrix.toBilin' (Lattice.gramA 15) v w) ∧
        (4 : ℤ) • x = f Lattice.a15GlueNumerator

/-- The normalized spinor vector implies `D12` coordinate rigidity. -/
theorem d12FullRankGlueRigidity_of_normalizedGlueVector
    (h : D12NormalizedGlueVectorInput) :
    D12FullRankGlueRigidityInput := by
  intro L hfree hroot
  obtain ⟨f, x, hpair, hx⟩ := h L hfree hroot
  exact Lattice.isMatrixModel_d12Plus_of_glueVector L f hpair x hx

/-- The normalized diagonal vector implies `E7 + E7` coordinate rigidity. -/
theorem e7e7FullRankGlueRigidity_of_normalizedGlueVector
    (h : E7E7NormalizedGlueVectorInput) :
    E7E7FullRankGlueRigidityInput := by
  intro L hfree hroot
  obtain ⟨f, x, hpair, hx⟩ := h L hfree hroot
  exact Lattice.isMatrixModel_e7e7Plus_of_glueVector L f hpair x hx

/-- The normalized order-four vector implies `A15` coordinate rigidity. -/
theorem a15FullRankGlueRigidity_of_normalizedGlueVector
    (h : A15NormalizedGlueVectorInput) :
    A15FullRankGlueRigidityInput := by
  intro L hfree hroot
  obtain ⟨f, x, hpair, hx⟩ := h L hfree hroot
  exact Lattice.isMatrixModel_a15Plus_of_glueVector L f hpair x hx

/-- **Theta-eutaxy with the minimized glue boundary.**  The structural
theta/ADE theorem and three normalized divisibility statements imply the
complete rank-12-to-15 coordinate classification consumed downstream. -/
theorem rootedCorankFourClassification_of_thetaEutaxy_glueVectors
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hD12 : D12NormalizedGlueVectorInput)
    (hE7E7 : E7E7NormalizedGlueVectorInput)
    (hA15 : A15NormalizedGlueVectorInput) :
    RootedCorankFourClassification :=
  rootedCorankFourClassification_of_thetaEutaxy_glue hTheta
    (d12FullRankGlueRigidity_of_normalizedGlueVector hD12)
    (e7e7FullRankGlueRigidity_of_normalizedGlueVector hE7E7)
    (a15FullRankGlueRigidity_of_normalizedGlueVector hA15)

end SRG266
