/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RadialGaussianHessian

/-!
# Fourier transform of a degree-two harmonic Gaussian

This file proves the Fourier-transform formula for the trace-free quadratic
`harmonicQuadratic`.  The proof differentiates Mathlib's exact Gaussian
Fourier formula twice, takes the trace in an orthonormal basis, and uses the
harmonic cancellation proved in `HarmonicQuadratic.lean`.

In rank 24 the final formula has weight 14:

`Fourier (P(v) exp (-π t ‖v‖²)) (w) =
  -t⁻¹⁴ P(w) exp (-π t⁻¹ ‖w‖²)`.

All differentiation, integrability, finite summation, and scalar
simplification is checked in Lean.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The second derivative of the Fourier transform of a Gaussian is the
Fourier transform of its quadratic moment. -/
theorem hessian_fourier_realGaussian {t : ℝ} (ht : 0 < t) (w x y : V) :
    iteratedFDeriv ℝ 2 (𝓕 (realGaussian (V := V) t)) w ![x, y] =
      (-4 * (Real.pi : ℂ) ^ 2) *
        𝓕 (fun v : V =>
          ((inner ℝ v x * inner ℝ v y : ℝ) : ℂ) * realGaussian t v) w := by
  have hmeas : AEStronglyMeasurable (realGaussian (V := V) t) :=
    (realGaussian_continuous t).aestronglyMeasurable
  have hmom (n : ℕ) : Integrable fun v : V =>
      ‖v‖ ^ n * ‖realGaussian t v‖ :=
    realGaussian_moment_integrable n ht
  have hderiv := Real.iteratedFDeriv_fourier
    (f := realGaussian (V := V) t) (N := (2 : ℕ∞))
    (fun n _ => hmom n) hmeas (n := 2) (by norm_num)
  have h := congrArg
    (fun F : V → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℂ => F w ![x, y])
    hderiv
  rw [Real.fourier_continuousMultilinearMap_apply
    (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hmom 2) hmeas)] at h
  simp only [VectorFourier.fourierPowSMulRight_apply, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  have hfun : (fun v : V =>
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ 2 •
        (((innerSL ℝ) v) x * ((innerSL ℝ) v) y) • realGaussian t v) =
      (-4 * (Real.pi : ℂ) ^ 2) •
        (fun v : V =>
          ((inner ℝ v x * inner ℝ v y : ℝ) : ℂ) * realGaussian t v) := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    rw [innerSL_apply_apply, innerSL_apply_apply]
    have hscalar : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ 2 =
        -4 * (Real.pi : ℂ) ^ 2 := by
      rw [pow_two]
      calc
        -(2 * (Real.pi : ℂ) * Complex.I) *
            -(2 * (Real.pi : ℂ) * Complex.I) =
            4 * (Real.pi : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
        _ = -4 * (Real.pi : ℂ) ^ 2 := by rw [Complex.I_mul_I]; ring
    rw [hscalar]
  rw [hfun, Real.fourier_eq, Real.fourier_eq]
  simp_rw [Pi.smul_apply, smul_comm _ (-4 * (Real.pi : ℂ) ^ 2)]
  rw [integral_smul]
  rfl

/-- The prefactor in the Fourier transform of a centered Gaussian. -/
def gaussianFourierPrefactor (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (t : ℝ) : ℂ :=
  ((Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ)) ^
    (Module.finrank ℝ V / 2 : ℂ)

/-- The exponential rate in the Fourier transform of a centered Gaussian. -/
def gaussianFourierRate (t : ℝ) : ℂ :=
  -(Real.pi : ℂ) ^ 2 / ((Real.pi * t : ℝ) : ℂ)

theorem fourier_realGaussian_eq_prefactor_mul_radialExp {t : ℝ} (ht : 0 < t) :
    𝓕 (realGaussian (V := V) t) = fun w =>
      gaussianFourierPrefactor V t * radialExp (gaussianFourierRate t) w := by
  funext w
  have hb : 0 < (((Real.pi * t : ℝ) : ℂ)).re := by
    simpa using mul_pos Real.pi_pos ht
  change 𝓕 (fun v : V =>
      Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2)) w = _
  rw [fourier_gaussian_innerProductSpace hb]
  unfold gaussianFourierPrefactor gaussianFourierRate radialExp
  congr 2
  have hpow : (‖w‖ : ℂ) ^ 2 = ((‖w‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [hpow]
  ring

theorem hessian_fourier_realGaussian_explicit {t : ℝ} (ht : 0 < t)
    (w x y : V) :
    iteratedFDeriv ℝ 2 (𝓕 (realGaussian (V := V) t)) w ![x, y] =
      gaussianFourierPrefactor V t *
        (Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ)) *
          (4 * gaussianFourierRate t ^ 2 * inner ℝ w x * inner ℝ w y +
            2 * gaussianFourierRate t * inner ℝ x y)) := by
  rw [fourier_realGaussian_eq_prefactor_mul_radialExp ht]
  have hsmooth : ContDiffAt ℝ 2 (radialExp (gaussianFourierRate t) : V → ℂ) w := by
    have hnorm : ContDiff ℝ 2 (fun z : V => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
    exact (Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hnorm))).contDiffAt
  change iteratedFDeriv ℝ 2
      ((gaussianFourierPrefactor V t) • radialExp (gaussianFourierRate t)) w ![x, y] = _
  rw [iteratedFDeriv_const_smul_apply hsmooth]
  change gaussianFourierPrefactor V t *
      iteratedFDeriv ℝ 2 (radialExp (gaussianFourierRate t)) w ![x, y] = _
  rw [iteratedFDeriv_two_radialExp_apply]

/-- Exact Fourier transform of one polarized quadratic Gaussian moment. -/
theorem fourier_inner_mul_inner_realGaussian {t : ℝ} (ht : 0 < t)
    (w x y : V) :
    𝓕 (fun v : V =>
      ((inner ℝ v x * inner ℝ v y : ℝ) : ℂ) * realGaussian t v) w =
      (-1 / (4 * (Real.pi : ℂ) ^ 2)) * gaussianFourierPrefactor V t *
        (Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ)) *
          (4 * gaussianFourierRate t ^ 2 * inner ℝ w x * inner ℝ w y +
            2 * gaussianFourierRate t * inner ℝ x y)) := by
  have h₁ := hessian_fourier_realGaussian ht w x y
  have h₂ := hessian_fourier_realGaussian_explicit ht w x y
  have h := h₁.symm.trans h₂
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : (-4 * (Real.pi : ℂ) ^ 2) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi)
  apply (mul_left_cancel₀ hc)
  rw [h]
  field_simp [Real.pi_ne_zero]

/-- A polarized quadratic moment times the centered Gaussian. -/
def innerMulGaussian (t : ℝ) (x y : V) : V → ℂ := fun v =>
  ((inner ℝ v x * inner ℝ v y : ℝ) : ℂ) * realGaussian t v

theorem innerMulGaussian_integrable {t : ℝ} (ht : 0 < t) (x y : V) :
    Integrable (innerMulGaussian t x y) := by
  let C := ‖x‖ * ‖y‖
  have hmom := realGaussian_moment_integrable (V := V) 2 ht
  apply Integrable.mono' (hmom.const_mul C)
  · have hreal : Continuous (fun v : V => inner ℝ v x * inner ℝ v y) := by
      fun_prop
    exact ((Complex.ofRealCLM.continuous.comp hreal).mul
      (realGaussian_continuous t)).aestronglyMeasurable
  · filter_upwards with v
    rw [innerMulGaussian, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hx := abs_real_inner_le_norm v x
    have hy := abs_real_inner_le_norm v y
    rw [abs_mul]
    calc
      |inner ℝ v x| * |inner ℝ v y| * ‖realGaussian t v‖ ≤
          (‖v‖ * ‖x‖) * (‖v‖ * ‖y‖) * ‖realGaussian t v‖ := by
        gcongr
      _ = C * (‖v‖ ^ 2 * ‖realGaussian t v‖) := by ring

/-- The squared norm times the centered Gaussian. -/
def normSqGaussian (t : ℝ) : V → ℂ := fun v =>
  ((‖v‖ ^ 2 : ℝ) : ℂ) * realGaussian t v

theorem normSqGaussian_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (normSqGaussian (V := V) t) := by
  have hmom := realGaussian_moment_integrable (V := V) 2 ht
  apply Integrable.mono' hmom
  · unfold normSqGaussian
    have hnorm : Continuous (fun v : V => ‖v‖ ^ 2) := by fun_prop
    exact ((Complex.ofRealCLM.continuous.comp hnorm).mul
      (realGaussian_continuous t)).aestronglyMeasurable
  · filter_upwards with v
    rw [normSqGaussian, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg ‖v‖)]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem sum_inner_self_orthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (v : V) :
    ∑ i, inner ℝ v (b i) * inner ℝ v (b i) = ‖v‖ ^ 2 := by
  simpa only [real_inner_comm v, real_inner_self_eq_norm_sq] using
    sum_orthonormalBasis_inner_mul_inner b v v

/-- The Fourier transform of `‖v‖²` times a Gaussian is the trace of the
polarized moment transforms. -/
theorem fourier_normSqGaussian_eq_sum
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {t : ℝ} (ht : 0 < t) (w : V) :
    𝓕 (normSqGaussian (V := V) t) w =
      ∑ i, 𝓕 (innerMulGaussian t (b i) (b i)) w := by
  rw [Real.fourier_eq]
  have hfun : (fun v : V => 𝐞 (-inner ℝ v w) • normSqGaussian t v) =
      fun v => ∑ i, 𝐞 (-inner ℝ v w) • innerMulGaussian t (b i) (b i) v := by
    funext v
    unfold normSqGaussian innerMulGaussian
    rw [← Finset.smul_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    norm_cast
    exact (sum_inner_self_orthonormalBasis b v).symm
  rw [hfun, integral_finsetSum]
  · congr 1
  · intro i hi
    exact (Real.fourierIntegral_convergent_iff w).2
      (innerMulGaussian_integrable ht (b i) (b i))

/-- Linear decomposition of the harmonic Gaussian transform into its
polarized moment and trace terms. -/
theorem fourier_harmonicGaussian_decompose
    {t : ℝ} (ht : 0 < t) (w x y : V) :
    𝓕 (harmonicGaussian t x y) w =
      (Module.finrank ℝ V : ℂ) * 𝓕 (innerMulGaussian t x y) w -
        (inner ℝ x y : ℂ) * 𝓕 (normSqGaussian (V := V) t) w := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  have hprod := (Real.fourierIntegral_convergent_iff w).2
    (innerMulGaussian_integrable ht x y)
  have hnorm := (Real.fourierIntegral_convergent_iff w).2
    (normSqGaussian_integrable (V := V) ht)
  have hfun : (fun v : V => 𝐞 (-inner ℝ v w) • harmonicGaussian t x y v) =
      fun v =>
        (Module.finrank ℝ V : ℂ) •
          (𝐞 (-inner ℝ v w) • innerMulGaussian t x y v) -
        (inner ℝ x y : ℂ) •
          (𝐞 (-inner ℝ v w) • normSqGaussian t v) := by
    funext v
    have hcore : harmonicGaussian t x y v =
        (Module.finrank ℝ V : ℂ) • innerMulGaussian t x y v -
          (inner ℝ x y : ℂ) • normSqGaussian t v := by
      unfold harmonicGaussian harmonicQuadratic innerMulGaussian normSqGaussian
      simp only [smul_eq_mul]
      rw [real_inner_self_eq_norm_sq]
      push_cast
      ring
    rw [hcore, smul_sub, smul_comm (𝐞 (-inner ℝ v w))
      (Module.finrank ℝ V : ℂ), smul_comm (𝐞 (-inner ℝ v w)) (inner ℝ x y : ℂ)]
  rw [hfun, integral_sub, integral_smul, integral_smul]
  · rfl
  · exact hprod.smul (Module.finrank ℝ V : ℂ)
  · exact hnorm.smul (inner ℝ x y : ℂ)

theorem fourier_innerMulGaussian {t : ℝ} (ht : 0 < t) (w x y : V) :
    𝓕 (innerMulGaussian t x y) w =
      (-1 / (4 * (Real.pi : ℂ) ^ 2)) * gaussianFourierPrefactor V t *
        (Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ)) *
          (4 * gaussianFourierRate t ^ 2 * inner ℝ w x * inner ℝ w y +
            2 * gaussianFourierRate t * inner ℝ x y)) := by
  exact fourier_inner_mul_inner_realGaussian ht w x y

theorem fourier_normSqGaussian_explicit
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {t : ℝ} (ht : 0 < t) (w : V) :
    𝓕 (normSqGaussian (V := V) t) w =
      (-1 / (4 * (Real.pi : ℂ) ^ 2)) * gaussianFourierPrefactor V t *
        (Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ)) *
          (4 * gaussianFourierRate t ^ 2 * ‖w‖ ^ 2 +
            2 * gaussianFourierRate t * Module.finrank ℝ V)) := by
  rw [fourier_normSqGaussian_eq_sum b ht w]
  simp_rw [fourier_innerMulGaussian ht w]
  let C : ℂ := (-1 / (4 * (Real.pi : ℂ) ^ 2)) * gaussianFourierPrefactor V t
  let E : ℂ := Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ))
  let q : ℂ := gaussianFourierRate t
  have hself : ∀ i, inner ℝ (b i) (b i) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  simp_rw [hself]
  have hsum : ∑ i, inner ℝ w (b i) * inner ℝ w (b i) = ‖w‖ ^ 2 :=
    sum_inner_self_orthonormalBasis b w
  have hsumC : ∑ i, (inner ℝ w (b i) : ℂ) * (inner ℝ w (b i) : ℂ) =
      ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hsum
  have hcard : Fintype.card ι = Module.finrank ℝ V :=
    (Module.finrank_eq_card_basis b.toBasis).symm
  have hfirst :
      (∑ i, 4 * q ^ 2 * (inner ℝ w (b i) : ℂ) * (inner ℝ w (b i) : ℂ)) =
        4 * q ^ 2 * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hsumC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change (∑ i, C * (E * (4 * q ^ 2 * inner ℝ w (b i) *
      inner ℝ w (b i) + 2 * q * 1))) =
    C * (E * (4 * q ^ 2 * ‖w‖ ^ 2 + 2 * q * Module.finrank ℝ V))
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, hfirst]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  push_cast
  ring

/-- Fourier transform of a degree-two harmonic Gaussian in arbitrary finite
dimension.  The trace terms cancel exactly. -/
theorem fourier_harmonicGaussian
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {t : ℝ} (ht : 0 < t) (w x y : V) :
    𝓕 (harmonicGaussian t x y) w =
      (-gaussianFourierRate t ^ 2 / (Real.pi : ℂ) ^ 2) *
        gaussianFourierPrefactor V t *
        ((harmonicQuadratic x y w : ℂ) *
          Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ))) := by
  rw [fourier_harmonicGaussian_decompose ht w x y,
    fourier_innerMulGaussian ht w x y,
    fourier_normSqGaussian_explicit b ht w]
  unfold harmonicQuadratic
  rw [real_inner_self_eq_norm_sq]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  ring

theorem gaussianFourierRate_eq {t : ℝ} (ht : t ≠ 0) :
    gaussianFourierRate t = -((Real.pi / t : ℝ) : ℂ) := by
  unfold gaussianFourierRate
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp [hpi, htC]

omit [MeasurableSpace V] [BorelSpace V] in
theorem gaussianFourierPrefactor_rank24 {t : ℝ} (ht : t ≠ 0)
    (hdim : Module.finrank ℝ V = 24) :
    gaussianFourierPrefactor V t = ((t : ℂ)⁻¹) ^ 12 := by
  unfold gaussianFourierPrefactor
  rw [hdim]
  norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [hpi, htC]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
theorem radialExp_rate_eq_realGaussian_inv {t : ℝ} (ht : t ≠ 0) (w : V) :
    Complex.exp (gaussianFourierRate t * (‖w‖ ^ 2 : ℝ)) =
      realGaussian (V := V) t⁻¹ w := by
  rw [gaussianFourierRate_eq ht]
  unfold realGaussian
  congr 1
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp [htC]

/-- **Rank-24 harmonic Gaussian transform.**  The extra quadratic degree
changes the ordinary Gaussian weight 12 to weight 14 and contributes the
sign `-1`. -/
theorem fourier_harmonicGaussian_rank24
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (hdim : Module.finrank ℝ V = 24) {t : ℝ} (ht : 0 < t)
    (w x y : V) :
    𝓕 (harmonicGaussian t x y) w =
      -((t : ℂ)⁻¹) ^ 14 * harmonicGaussian t⁻¹ x y w := by
  rw [fourier_harmonicGaussian b ht w x y]
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [gaussianFourierPrefactor_rank24 ht0 hdim,
    radialExp_rate_eq_realGaussian_inv ht0 w]
  unfold harmonicGaussian
  rw [gaussianFourierRate_eq ht0]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  push_cast
  field_simp [hpi, htC]

end SRG266.Lattice
