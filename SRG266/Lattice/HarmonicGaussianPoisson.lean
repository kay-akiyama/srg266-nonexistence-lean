/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.HarmonicGaussianFourier
import SRG266.Lattice.SchwartzPoisson

/-!
# Poisson summation for the rank-24 harmonic Gaussian

The general periodization proof only needs polynomial decay, rather than a
bundled proof that every derivative is rapidly decreasing.  This file proves
that decay directly for the harmonic Gaussian and obtains its exact rank-24
Poisson functional equation.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A harmonic Gaussian decays faster than every prescribed power. -/
theorem exists_harmonicGaussian_pow_decay {t : ℝ} (ht : 0 < t)
    (k : ℕ) (x y : V) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : V, u ≠ 0 →
      ‖harmonicGaussian t x y u‖ ≤ A / ‖u‖ ^ k := by
  let a := Real.pi * t
  have ha : 0 < a := mul_pos Real.pi_pos ht
  obtain ⟨B, hB0, hB⟩ := exists_bound_pow_mul_rexp_neg_sq (k + 2) ha
  let C : ℝ := ((Module.finrank ℝ V : ℝ) + 1) * ‖x‖ * ‖y‖
  have hC : 0 ≤ C := by positivity
  refine ⟨C * B, mul_nonneg hC hB0, fun u hu => ?_⟩
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [le_div_iff₀ (pow_pos hunorm k)]
  rw [harmonicGaussian, realGaussian, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have hre :
      (-((Real.pi * t : ℝ) : ℂ) * (‖u‖ : ℂ) ^ 2).re =
        -a * ‖u‖ ^ 2 := by
    dsimp only [a]
    norm_cast
  rw [hre]
  have hp := abs_harmonicQuadratic_le x y u
  have hbound := hB ‖u‖
  rw [abs_of_nonneg (norm_nonneg _)] at hbound
  calc
    |harmonicQuadratic x y u| * Real.exp (-a * ‖u‖ ^ 2) * ‖u‖ ^ k ≤
        (C * ‖u‖ ^ 2) * Real.exp (-a * ‖u‖ ^ 2) * ‖u‖ ^ k := by
      gcongr
    _ = C * (‖u‖ ^ (k + 2) * Real.exp (-a * ‖u‖ ^ 2)) := by
      rw [pow_add]
      ring
    _ ≤ C * B := by gcongr

/-- The harmonic Gaussian bundled only as a continuous map. -/
def harmonicGaussianContinuous {n : ℕ} (t : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  ⟨harmonicGaussian t x y, harmonicGaussian_continuous t x y⟩

theorem harmonicGaussian_locallyNormallySummableIntegerTranslates
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin n)) :
    LocallyNormallySummableIntegerTranslates
      (harmonicGaussianContinuous t x y) := by
  obtain ⟨A, hA, hdecay⟩ :=
    exists_harmonicGaussian_pow_decay ht (n + 1) x y
  exact locallyNormallySummableIntegerTranslates_of_pow_decay
    (harmonicGaussianContinuous t x y) (Nat.lt_succ_self n) hA hdecay

theorem summable_harmonicGaussian_intVector
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin n)) :
    Summable fun z : Fin n → ℤ =>
      harmonicGaussian t x y (intVectorToReal z) := by
  exact summable_integerValues_of_locallyNormal
    (harmonicGaussianContinuous t x y)
    (harmonicGaussian_locallyNormallySummableIntegerTranslates ht x y)

theorem summable_fourier_harmonicGaussian_rank24
    {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    Summable fun m : Fin 24 → ℤ =>
      𝓕 (harmonicGaussian t x y) (intVectorToReal m) := by
  have hinv : 0 < t⁻¹ := inv_pos.mpr ht
  have hsum := summable_harmonicGaussian_intVector hinv x y
  have hscaled := hsum.mul_left (-((t : ℂ)⁻¹) ^ 14)
  refine hscaled.congr fun m => ?_
  exact (fourier_harmonicGaussian_rank24
    (EuclideanSpace.basisFun (Fin 24) ℝ)
    (by simp) ht (intVectorToReal m) x y).symm

/-- **Rank-24 harmonic Gaussian Poisson equation on the standard integral
lattice.** -/
theorem harmonicGaussian_piPoisson_rank24
    {t : ℝ} (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin 24)) :
    (∑' z : Fin 24 → ℤ,
      harmonicGaussian t x y (intVectorToReal z)) =
      -((t : ℂ)⁻¹) ^ 14 *
        ∑' m : Fin 24 → ℤ,
          harmonicGaussian t⁻¹ x y (intVectorToReal m) := by
  have hp := continuous_piPoisson (harmonicGaussianContinuous t x y)
    (harmonicGaussian_integrable ht x y)
    (harmonicGaussian_locallyNormallySummableIntegerTranslates ht x y)
    (summable_fourier_harmonicGaussian_rank24 ht x y)
  change (∑' z : Fin 24 → ℤ,
      harmonicGaussian t x y (intVectorToReal z)) =
    ∑' m : Fin 24 → ℤ,
      𝓕 (harmonicGaussian t x y) (intVectorToReal m) at hp
  rw [hp]
  have hsum := summable_harmonicGaussian_intVector (inv_pos.mpr ht) x y
  calc
    (∑' m : Fin 24 → ℤ,
        𝓕 (harmonicGaussian t x y) (intVectorToReal m)) =
        ∑' m : Fin 24 → ℤ,
          -((t : ℂ)⁻¹) ^ 14 *
            harmonicGaussian t⁻¹ x y (intVectorToReal m) := by
      apply tsum_congr
      intro m
      exact fourier_harmonicGaussian_rank24
        (EuclideanSpace.basisFun (Fin 24) ℝ)
        (by simp) ht (intVectorToReal m) x y
    _ = -((t : ℂ)⁻¹) ^ 14 *
        ∑' m : Fin 24 → ℤ,
          harmonicGaussian t⁻¹ x y (intVectorToReal m) :=
      hsum.tsum_mul_left _

end SRG266.Lattice
