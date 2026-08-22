/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.EuclideanLatticeRealization
import SRG266.Lattice.FourierLinearChange
import SRG266.Lattice.HarmonicGaussianPoisson

/-!
# Harmonic Gaussian Poisson summation on a unimodular rank-24 lattice

This file transports the standard-coordinate multivariate Poisson theorem to
the determinant-one Euclidean realization of an arbitrary positive-definite
unimodular lattice.  The inverse integral Gram automorphism reindexes the dual
lattice, so the resulting functional equation is again a sum over the
original lattice.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- Polynomial decay is preserved by precomposition with a real linear
equivalence. -/
theorem exists_harmonicGaussian_comp_linearEquiv_pow_decay
    {t : ℝ} (ht : 0 < t) (k : ℕ) (A : V ≃ₗ[ℝ] V) (x y : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : V, u ≠ 0 →
      ‖harmonicGaussian t x y (A u)‖ ≤ C / ‖u‖ ^ k := by
  obtain ⟨C, hC, hdecay⟩ := exists_harmonicGaussian_pow_decay ht k x y
  let D : ℝ :=
    ‖A.symm.toContinuousLinearEquiv.toContinuousLinearMap‖
  have hD : 0 ≤ D := norm_nonneg _
  refine ⟨C * D ^ k, mul_nonneg hC (pow_nonneg hD k), fun u hu => ?_⟩
  have hAu : A u ≠ 0 := by
    simpa using A.injective.ne hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnAu : 0 < ‖A u‖ := norm_pos_iff.mpr hAu
  have hbase := hdecay (A u) hAu
  have hmass :
      ‖harmonicGaussian t x y (A u)‖ * ‖A u‖ ^ k ≤ C :=
    (le_div_iff₀ (pow_pos hnAu k)).mp hbase
  have hnorm : ‖u‖ ≤ D * ‖A u‖ := by
    calc
      ‖u‖ = ‖A.symm (A u)‖ := by rw [A.symm_apply_apply]
      _ ≤ D * ‖A u‖ :=
        A.symm.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm (A u)
  have hpow : ‖u‖ ^ k ≤ D ^ k * ‖A u‖ ^ k := by
    calc
      ‖u‖ ^ k ≤ (D * ‖A u‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm k
      _ = D ^ k * ‖A u‖ ^ k := mul_pow D ‖A u‖ k
  rw [le_div_iff₀ (pow_pos hnu k)]
  calc
    ‖harmonicGaussian t x y (A u)‖ * ‖u‖ ^ k ≤
        ‖harmonicGaussian t x y (A u)‖ * (D ^ k * ‖A u‖ ^ k) := by
      gcongr
    _ = D ^ k *
        (‖harmonicGaussian t x y (A u)‖ * ‖A u‖ ^ k) := by ring
    _ ≤ D ^ k * C := by gcongr
    _ = C * D ^ k := by ring

/-- Harmonic Gaussian composed with the Euclidean lattice realization,
bundled as a continuous map. -/
def latticeHarmonicGaussianContinuous (L : PDUnimodularLattice 24)
    (t : ℝ) (x y : EuclideanSpace ℝ (Fin 24)) :
    C(EuclideanSpace ℝ (Fin 24), ℂ) :=
  ⟨fun u => harmonicGaussian t x y (pdEuclideanEquiv L u),
    (harmonicGaussian_continuous t x y).comp
      (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin 24) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 24)).continuous_of_finiteDimensional⟩

/-- Integer translates of the pulled-back harmonic Gaussian are locally
normally summable. -/
theorem latticeHarmonicGaussian_locallyNormallySummableIntegerTranslates
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    LocallyNormallySummableIntegerTranslates
      (latticeHarmonicGaussianContinuous L t x y) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_harmonicGaussian_comp_linearEquiv_pow_decay ht 25
      (pdEuclideanEquiv L) x y
  exact locallyNormallySummableIntegerTranslates_of_pow_decay
    (latticeHarmonicGaussianContinuous L t x y) (by norm_num) hC hdecay

/-- Absolute summability of the harmonic Gaussian on the realized lattice. -/
theorem summable_harmonicGaussian_pdEuclideanEquiv_intVector
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    Summable fun z : Fin 24 → ℤ =>
      harmonicGaussian t x y
        (pdEuclideanEquiv L (intVectorToReal z)) := by
  exact summable_integerValues_of_locallyNormal
    (latticeHarmonicGaussianContinuous L t x y)
    (latticeHarmonicGaussian_locallyNormallySummableIntegerTranslates
      L ht x y)

/-- The determinant-one realization preserves Lebesgue measure. -/
theorem pdEuclideanEquiv_measurePreserving (L : PDUnimodularLattice 24) :
    MeasurePreserving
      (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin 24) →
        EuclideanSpace ℝ (Fin 24)) volume volume := by
  constructor
  · exact (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin 24) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 24)).continuous_of_finiteDimensional.measurable
  · have hdet : LinearMap.det (pdEuclideanEquiv L :
        EuclideanSpace ℝ (Fin 24) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 24)) ≠ 0 := by
      rw [pdEuclideanEquiv_det_eq_one]
      norm_num
    have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      volume hdet
    rw [pdEuclideanEquiv_det_eq_one] at hmap
    simpa using hmap

/-- Integrability of the pulled-back harmonic Gaussian. -/
theorem latticeHarmonicGaussian_integrable
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    Integrable fun u =>
      harmonicGaussian t x y (pdEuclideanEquiv L u) := by
  exact (pdEuclideanEquiv_measurePreserving L).integrable_comp_of_integrable
    (harmonicGaussian_integrable ht x y)

/-- Pointwise Fourier transform of the pulled-back rank-24 harmonic
Gaussian, with the dual frequency reindexed integrally. -/
theorem fourier_latticeHarmonicGaussian_rank24
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) (m : Fin 24 → ℤ) :
    𝓕 (fun u => harmonicGaussian t x y (pdEuclideanEquiv L u))
        (intVectorToReal m) =
      -((t : ℂ)⁻¹) ^ 14 *
        harmonicGaussian t⁻¹ x y
          (pdEuclideanEquiv L
            (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
  change 𝓕 (harmonicGaussian t x y ∘ pdEuclideanEquiv L)
      (intVectorToReal m) = _
  rw [fourier_comp_linearEquiv, pdEuclideanEquiv_det_eq_one]
  simp only [abs_one, inv_one, one_smul]
  rw [pdEuclideanEquiv_symm_adjoint_intVector]
  exact fourier_harmonicGaussian_rank24
    (EuclideanSpace.basisFun (Fin 24) ℝ) (by simp) ht _ x y

/-- The dual Fourier values are absolutely summable. -/
theorem summable_fourier_latticeHarmonicGaussian_rank24
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    Summable fun m : Fin 24 → ℤ =>
      𝓕 (fun u => harmonicGaussian t x y (pdEuclideanEquiv L u))
        (intVectorToReal m) := by
  have hsum :=
    (summable_harmonicGaussian_pdEuclideanEquiv_intVector L
      (inv_pos.mpr ht) x y).comp_injective
        (pdGramCoordEquiv L).symm.injective
  have hscaled := hsum.mul_left (-((t : ℂ)⁻¹) ^ 14)
  exact hscaled.congr fun m =>
    (fourier_latticeHarmonicGaussian_rank24 L ht x y m).symm

/-- **Rank-24 harmonic Gaussian Poisson equation on an arbitrary
positive-definite unimodular lattice.** -/
theorem harmonicGaussian_latticePoisson_rank24
    (L : PDUnimodularLattice 24) {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    (∑' z : Fin 24 → ℤ,
      harmonicGaussian t x y
        (pdEuclideanEquiv L (intVectorToReal z))) =
      -((t : ℂ)⁻¹) ^ 14 *
        ∑' z : Fin 24 → ℤ,
          harmonicGaussian t⁻¹ x y
            (pdEuclideanEquiv L (intVectorToReal z)) := by
  have hp := continuous_piPoisson
    (latticeHarmonicGaussianContinuous L t x y)
    (latticeHarmonicGaussian_integrable L ht x y)
    (latticeHarmonicGaussian_locallyNormallySummableIntegerTranslates
      L ht x y)
    (summable_fourier_latticeHarmonicGaussian_rank24 L ht x y)
  change (∑' z : Fin 24 → ℤ,
      harmonicGaussian t x y
        (pdEuclideanEquiv L (intVectorToReal z))) =
    ∑' m : Fin 24 → ℤ,
      𝓕 (fun u => harmonicGaussian t x y (pdEuclideanEquiv L u))
        (intVectorToReal m) at hp
  rw [hp]
  calc
    (∑' m : Fin 24 → ℤ,
      𝓕 (fun u => harmonicGaussian t x y (pdEuclideanEquiv L u))
        (intVectorToReal m)) =
      ∑' m : Fin 24 → ℤ,
        -((t : ℂ)⁻¹) ^ 14 *
          harmonicGaussian t⁻¹ x y
            (pdEuclideanEquiv L
              (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
        apply tsum_congr
        exact fourier_latticeHarmonicGaussian_rank24 L ht x y
    _ = -((t : ℂ)⁻¹) ^ 14 *
        ∑' m : Fin 24 → ℤ,
          harmonicGaussian t⁻¹ x y
            (pdEuclideanEquiv L
              (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
        rw [tsum_mul_left]
    _ = -((t : ℂ)⁻¹) ^ 14 *
        ∑' z : Fin 24 → ℤ,
          harmonicGaussian t⁻¹ x y
            (pdEuclideanEquiv L (intVectorToReal z)) := by
        congr 1
        exact (pdGramCoordEquiv L).symm.toEquiv.tsum_eq
          (fun z : Fin 24 → ℤ =>
            harmonicGaussian t⁻¹ x y
              (pdEuclideanEquiv L (intVectorToReal z)))

end SRG266.Lattice
