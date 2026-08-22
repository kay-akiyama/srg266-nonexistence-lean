/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Fourier transform under an invertible linear change of variables

Mathlib contains the measure-preserving formula for a linear isometry.  Lattice
Poisson summation also needs the corresponding formula for an arbitrary real
linear equivalence.  The determinant factor comes directly from the Haar
measure change-of-variables theorem, while the frequency is transported by
the adjoint of the inverse map.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Fourier transform under an invertible linear change of variables.**

With mathlib's normalization, precomposition by `A` contributes the inverse
absolute determinant and sends the frequency through the adjoint of `A⁻¹`.
No integrability hypothesis is needed in the statement: as for mathlib's
Fourier-transform congruence lemmas, both sides use the convention that a
non-integrable Bochner integral is zero. -/
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (f ∘ A) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
        𝓕 f ((A.symm : V →ₗ[ℝ] V).adjoint w) := by
  let c : ENNReal := ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹|
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 :=
    A.isUnit_det'.ne_zero
  have hmap : Measure.map (A : V →ₗ[ℝ] V) volume = c • volume := by
    simpa [c] using
      (MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet)
  let g : V → ℂ := fun u ↦
    𝐞 (-⟪u, (A.symm : V →ₗ[ℝ] V).adjoint w⟫) • f u
  have hgA : ∀ v : V,
      g (A v) = 𝐞 (-⟪v, w⟫) • (f ∘ A) v := by
    intro v
    have hinner :
        inner ℝ (A v) ((A.symm : V →ₗ[ℝ] V).adjoint w) = inner ℝ v w := by
      rw [LinearMap.adjoint_inner_right]
      simp
    simp only [g, Function.comp_apply, hinner]
  have hchange :
      ∫ u, g u ∂(c • volume) = ∫ v, g (A v) := by
    rw [← hmap]
    exact integral_map_equiv
      A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv g
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [← hgA]
  rw [← hchange, integral_smul_measure]
  simp only [c, ENNReal.toReal_ofReal, abs_nonneg, g]
  rw [abs_inv]

end SRG266.Lattice
