/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.EuclideanLatticeRealization
import SRG266.Lattice.FourierLinearChange
import SRG266.Lattice.HarmonicGaussian
import SRG266.Lattice.SchwartzPoisson

/-!
# Complex Gaussian Poisson summation on a unimodular lattice

For a complex parameter in the open right half-plane, this file transports
the Fourier transform of a complex Gaussian through the determinant-one
Euclidean realization of an arbitrary positive-definite unimodular lattice.
The resulting Poisson equation is the analytic input used to prove that an
even unimodular positive-definite lattice has rank divisible by eight.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The scalar Gaussian with complex right-half-plane parameter `z`. -/
def complexGaussian {n : ℕ} (z : ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ := fun v =>
  Complex.exp (-((Real.pi : ℂ) * z) * (‖v‖ : ℂ) ^ 2)

/-- The complex Gaussian bundled as a continuous map. -/
def complexGaussianContinuous {n : ℕ} (z : ℂ) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  ⟨complexGaussian z, by
    unfold complexGaussian
    fun_prop⟩

/-- A complex Gaussian in the right half-plane decays faster than any
prescribed power. -/
theorem exists_complexGaussian_pow_decay {n k : ℕ} {z : ℂ}
    (hz : 0 < z.re) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      ‖complexGaussian z v‖ ≤ A / ‖v‖ ^ k := by
  let a : ℝ := Real.pi * z.re
  have ha : 0 < a := mul_pos Real.pi_pos hz
  obtain ⟨A, hA, hbound⟩ :=
    exists_bound_pow_mul_rexp_neg_sq k (a := a) ha
  refine ⟨A, hA, fun v hv => ?_⟩
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [le_div_iff₀ (pow_pos hvnorm k)]
  have hnorm : ‖complexGaussian z v‖ =
      Real.exp (-a * ‖v‖ ^ 2) := by
    unfold complexGaussian
    rw [Complex.norm_exp]
    congr 1
    dsimp only [a]
    have hcast : (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [hcast]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hnorm, mul_comm]
  simpa only [abs_of_nonneg (norm_nonneg v)] using hbound ‖v‖

/-- Polynomial decay is preserved by precomposition with a real linear
equivalence. -/
theorem exists_complexGaussian_comp_linearEquiv_pow_decay
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n k : ℕ} {z : ℂ} (hz : 0 < z.re)
    (A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : V, u ≠ 0 →
      ‖complexGaussian z (A u)‖ ≤ C / ‖u‖ ^ k := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_complexGaussian_pow_decay (n := n) (k := k) hz
  let D : ℝ := ‖A.symm.toContinuousLinearEquiv.toContinuousLinearMap‖
  have hD : 0 ≤ D := norm_nonneg _
  refine ⟨C * D ^ k, mul_nonneg hC (pow_nonneg hD k), fun u hu => ?_⟩
  have hAu : A u ≠ 0 := by simpa using A.injective.ne hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnAu : 0 < ‖A u‖ := norm_pos_iff.mpr hAu
  have hbase := hdecay (A u) hAu
  have hmass : ‖complexGaussian z (A u)‖ * ‖A u‖ ^ k ≤ C :=
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
    ‖complexGaussian z (A u)‖ * ‖u‖ ^ k ≤
        ‖complexGaussian z (A u)‖ * (D ^ k * ‖A u‖ ^ k) := by
      gcongr
    _ = D ^ k * (‖complexGaussian z (A u)‖ * ‖A u‖ ^ k) := by ring
    _ ≤ D ^ k * C := by gcongr
    _ = C * D ^ k := by ring

/-- The complex Gaussian pulled back along the Euclidean realization of a
unimodular lattice. -/
def latticeComplexGaussianContinuous {n : ℕ}
    (L : PDUnimodularLattice n) (z : ℂ) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  ⟨fun u => complexGaussian z (pdEuclideanEquiv L u),
    (complexGaussianContinuous z).continuous.comp
      (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n)).continuous_of_finiteDimensional⟩

/-- Integer translates of the pulled-back complex Gaussian are locally
normally summable. -/
theorem latticeComplexGaussian_locallyNormallySummableIntegerTranslates
    {n : ℕ} (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re) :
    LocallyNormallySummableIntegerTranslates
      (latticeComplexGaussianContinuous L z) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_complexGaussian_comp_linearEquiv_pow_decay
      (n := n) (k := n + 1) hz (pdEuclideanEquiv L)
  exact locallyNormallySummableIntegerTranslates_of_pow_decay
    (latticeComplexGaussianContinuous L z) (Nat.lt_succ_self n) hC hdecay

/-- Absolute summability on the realized lattice. -/
theorem summable_complexGaussian_pdEuclideanEquiv_intVector
    {n : ℕ} (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re) :
    Summable fun m : Fin n → ℤ =>
      complexGaussian z (pdEuclideanEquiv L (intVectorToReal m)) :=
  summable_integerValues_of_locallyNormal
    (latticeComplexGaussianContinuous L z)
    (latticeComplexGaussian_locallyNormallySummableIntegerTranslates L hz)

/-- The determinant-one Euclidean realization preserves Lebesgue measure. -/
theorem pdEuclideanEquiv_measurePreserving_generic {n : ℕ}
    (L : PDUnimodularLattice n) :
    MeasurePreserving
      (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)) volume volume := by
  constructor
  · exact (pdEuclideanEquiv L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)).continuous_of_finiteDimensional.measurable
  · have hdet : LinearMap.det (pdEuclideanEquiv L :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      rw [pdEuclideanEquiv_det_eq_one]
      norm_num
    have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      volume hdet
    rw [pdEuclideanEquiv_det_eq_one] at hmap
    simpa using hmap

/-- Integrability of the pulled-back complex Gaussian. -/
theorem latticeComplexGaussian_integrable {n : ℕ}
    (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re) :
    Integrable fun u : EuclideanSpace ℝ (Fin n) =>
      complexGaussian z (pdEuclideanEquiv L u) := by
  change Integrable
    (complexGaussian z ∘ (pdEuclideanEquiv L :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)))
  apply (pdEuclideanEquiv_measurePreserving_generic L).integrable_comp_of_integrable
  unfold complexGaussian
  have hb : 0 < ((Real.pi : ℂ) * z).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_pos Real.pi_pos hz
  simpa only [zero_mul, add_zero] using
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin n)) hb 0 0)

/-- The inverse of a right-half-plane parameter is again in the right half
plane. -/
theorem inv_re_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < z⁻¹.re := by
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr fun h => by simpa [h] using hz.ne')

/-- Fourier transform of the pulled-back complex Gaussian, with the dual
frequency reindexed by the integral inverse Gram automorphism. -/
theorem fourier_latticeComplexGaussian {n : ℕ}
    (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re)
    (m : Fin n → ℤ) :
    𝓕 (fun u : EuclideanSpace ℝ (Fin n) =>
        complexGaussian z (pdEuclideanEquiv L u)) (intVectorToReal m) =
      ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
        complexGaussian z⁻¹
          (pdEuclideanEquiv L
            (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
  change 𝓕 (complexGaussian z ∘ pdEuclideanEquiv L)
      (intVectorToReal m) = _
  rw [fourier_comp_linearEquiv, pdEuclideanEquiv_det_eq_one]
  simp only [abs_one, inv_one, one_smul]
  rw [pdEuclideanEquiv_symm_adjoint_intVector]
  unfold complexGaussian
  have hb : 0 < ((Real.pi : ℂ) * z).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_pos Real.pi_pos hz
  change 𝓕 (fun v : EuclideanSpace ℝ (Fin n) =>
      Complex.exp (-((Real.pi : ℂ) * z) * ‖v‖ ^ 2)) _ = _
  rw [fourier_gaussian_innerProductSpace hb]
  congr 1
  · simp
  · congr 1
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      ne_of_gt hz]

/-- The dual Fourier values are absolutely summable. -/
theorem summable_fourier_latticeComplexGaussian {n : ℕ}
    (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re) :
    Summable fun m : Fin n → ℤ =>
      𝓕 (fun u : EuclideanSpace ℝ (Fin n) =>
        complexGaussian z (pdEuclideanEquiv L u)) (intVectorToReal m) := by
  have hsum :=
    (summable_complexGaussian_pdEuclideanEquiv_intVector L
      (inv_re_pos_of_re_pos hz)).comp_injective
        (pdGramCoordEquiv L).symm.injective
  have hscaled := hsum.mul_left
    (((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2))
  exact hscaled.congr fun m => (fourier_latticeComplexGaussian L hz m).symm

/-- **Complex Gaussian Poisson equation on an arbitrary positive-definite
unimodular lattice.** -/
theorem complexGaussian_latticePoisson {n : ℕ}
    (L : PDUnimodularLattice n) {z : ℂ} (hz : 0 < z.re) :
    (∑' m : Fin n → ℤ,
      complexGaussian z (pdEuclideanEquiv L (intVectorToReal m))) =
      ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
        ∑' m : Fin n → ℤ,
          complexGaussian z⁻¹
            (pdEuclideanEquiv L (intVectorToReal m)) := by
  have hp := continuous_piPoisson
    (latticeComplexGaussianContinuous L z)
    (latticeComplexGaussian_integrable L hz)
    (latticeComplexGaussian_locallyNormallySummableIntegerTranslates L hz)
    (summable_fourier_latticeComplexGaussian L hz)
  change (∑' m : Fin n → ℤ,
      complexGaussian z (pdEuclideanEquiv L (intVectorToReal m))) =
    ∑' m : Fin n → ℤ,
      𝓕 (fun u : EuclideanSpace ℝ (Fin n) =>
        complexGaussian z (pdEuclideanEquiv L u)) (intVectorToReal m) at hp
  rw [hp]
  calc
    (∑' m : Fin n → ℤ,
      𝓕 (fun u : EuclideanSpace ℝ (Fin n) =>
        complexGaussian z (pdEuclideanEquiv L u)) (intVectorToReal m)) =
        ∑' m : Fin n → ℤ,
          ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
            complexGaussian z⁻¹
              (pdEuclideanEquiv L
                (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
          apply tsum_congr
          exact fourier_latticeComplexGaussian L hz
    _ = ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
        ∑' m : Fin n → ℤ,
          complexGaussian z⁻¹
            (pdEuclideanEquiv L
              (intVectorToReal ((pdGramCoordEquiv L).symm m))) := by
          rw [tsum_mul_left]
    _ = ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
        ∑' m : Fin n → ℤ,
          complexGaussian z⁻¹
            (pdEuclideanEquiv L (intVectorToReal m)) := by
          congr 1
          exact (pdGramCoordEquiv L).symm.toEquiv.tsum_eq
            (fun m : Fin n → ℤ =>
              complexGaussian z⁻¹
                (pdEuclideanEquiv L (intVectorToReal m)))

end SRG266.Lattice
