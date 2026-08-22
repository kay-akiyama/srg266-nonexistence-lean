/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HarmonicQuadratic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Harmonic Gaussians

This file supplies the elementary analytic estimates for the degree-two
harmonic Gaussian.  The estimates are stated on an arbitrary
finite-dimensional real inner-product space so that the later lattice
realification does not depend on a coordinate choice.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory Filter Asymptotics
open scoped RealInnerProductSpace Topology

/-- A polynomial times a one-dimensional Gaussian is globally bounded. -/
theorem exists_bound_pow_mul_rexp_neg_sq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ k * Real.exp (-a * r ^ 2) ≤ C := by
  let h : ℝ → ℝ := fun r ↦ |r| ^ k * Real.exp (-a * r ^ 2)
  have ht : Tendsto h (cocompact ℝ) (𝓝 0) := by
    simpa only [h, Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (k : ℝ)
  have hcont : Continuous h := by
    dsimp only [h]
    fun_prop
  have hbounded : Bornology.IsBounded (Set.range h) :=
    hcont.isBounded_range_iff_isBigO.mpr (ht.isBigO_one ℝ)
  rw [isBounded_iff_forall_norm_le] at hbounded
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨max C 0, le_max_right _ _, fun r ↦ ?_⟩
  have hr := hC (h r) ⟨r, rfl⟩
  have hh : 0 ≤ h r := mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le
  exact (show h r ≤ C by simpa [Real.norm_of_nonneg hh] using hr).trans
    (le_max_left _ _)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The centered Gaussian with Fourier-normalized real parameter `t`. -/
def realGaussian (t : ℝ) : V → ℂ := fun v ↦
  Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
theorem realGaussian_continuous (t : ℝ) :
    Continuous (realGaussian (V := V) t) := by
  unfold realGaussian
  fun_prop

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
@[simp]
theorem realGaussian_neg (t : ℝ) (v : V) :
    realGaussian t (-v) = realGaussian t v := by
  simp [realGaussian]

/-- Every polynomial norm moment of a positive real Gaussian is integrable. -/
theorem integrable_norm_pow_mul_rexp_neg_sq_norm (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun v : V ↦ ‖v‖ ^ k * Real.exp (-b * ‖v‖ ^ 2) := by
  let a : ℝ := b / 2
  have ha : 0 < a := div_pos hb (by norm_num)
  obtain ⟨C, hCnonneg, hC⟩ := exists_bound_pow_mul_rexp_neg_sq k ha
  have hbaseComplex := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (a : ℂ)) (by simpa using ha) 0 0
  have hbase : Integrable fun v : V ↦ Real.exp (-a * ‖v‖ ^ 2) := by
    convert hbaseComplex.norm using 1
    funext v
    rw [Complex.norm_exp]
    have hre :
        (-((a : ℂ)) * (‖v‖ : ℂ) ^ 2 + 0 * (inner ℝ (0 : V) v : ℂ)).re =
          -a * ‖v‖ ^ 2 := by
      have hpow : (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        norm_cast
      rw [hpow]
      norm_num
      left
      norm_cast
    rw [hre]
  apply Integrable.mono' (hbase.const_mul C)
  · fun_prop
  · filter_upwards with v
    rw [Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)]
    have hv := hC ‖v‖
    rw [abs_of_nonneg (norm_nonneg _)] at hv
    have hbdiv : b = a + a := by
      dsimp only [a]
      ring
    rw [hbdiv]
    have hexp : -(a + a) * ‖v‖ ^ 2 =
        -a * ‖v‖ ^ 2 + -a * ‖v‖ ^ 2 := by ring
    rw [hexp, Real.exp_add]
    calc
      ‖v‖ ^ k * (Real.exp (-a * ‖v‖ ^ 2) *
          Real.exp (-a * ‖v‖ ^ 2)) =
          (‖v‖ ^ k * Real.exp (-a * ‖v‖ ^ 2)) *
            Real.exp (-a * ‖v‖ ^ 2) := by ring
      _ ≤ C * Real.exp (-a * ‖v‖ ^ 2) := by
        gcongr

/-- Every norm moment of a positive Fourier-normalized Gaussian is integrable. -/
theorem realGaussian_moment_integrable (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun v : V ↦ ‖v‖ ^ k * ‖realGaussian (V := V) t v‖ := by
  have h := integrable_norm_pow_mul_rexp_neg_sq_norm
    (V := V) k (mul_pos Real.pi_pos ht)
  convert h using 1
  funext v
  rw [realGaussian, Complex.norm_exp]
  have hre :
      (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2).re =
        -(Real.pi * t) * ‖v‖ ^ 2 := by
    norm_cast
  rw [hre]

/-- The real-parameter harmonic Gaussian. -/
def harmonicGaussian (t : ℝ) (x y : V) : V → ℂ := fun v ↦
  (harmonicQuadratic x y v : ℂ) * realGaussian t v

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem harmonicGaussian_continuous (t : ℝ) (x y : V) :
    Continuous (harmonicGaussian t x y) := by
  unfold harmonicGaussian harmonicQuadratic realGaussian
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem harmonicGaussian_zero (t : ℝ) (x y : V) :
    harmonicGaussian t x y 0 = 0 := by
  simp [harmonicGaussian]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem harmonicGaussian_neg (t : ℝ) (x y v : V) :
    harmonicGaussian t x y (-v) = harmonicGaussian t x y v := by
  simp [harmonicGaussian]

/-- A positive harmonic Gaussian is integrable. -/
theorem harmonicGaussian_integrable {t : ℝ} (ht : 0 < t) (x y : V) :
    Integrable (harmonicGaussian t x y) := by
  let C : ℝ := ((Module.finrank ℝ V : ℝ) + 1) * ‖x‖ * ‖y‖
  have hmoment := integrable_norm_pow_mul_rexp_neg_sq_norm
    (V := V) 2 (mul_pos Real.pi_pos ht)
  apply Integrable.mono' (hmoment.const_mul C)
  · exact (harmonicGaussian_continuous t x y).aestronglyMeasurable
  · filter_upwards with v
    rw [harmonicGaussian, realGaussian, norm_mul, Complex.norm_exp]
    have hre :
        (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2).re =
          -(Real.pi * t) * ‖v‖ ^ 2 := by
      norm_cast
    rw [hre]
    have hp := abs_harmonicQuadratic_le x y v
    rw [Complex.norm_real, Real.norm_eq_abs]
    change |harmonicQuadratic x y v| * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) ≤
      C * (‖v‖ ^ 2 * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2))
    calc
      |harmonicQuadratic x y v| * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) ≤
          (C * ‖v‖ ^ 2) * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) := by
        gcongr
      _ = C * (‖v‖ ^ 2 * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2)) := by ring

end SRG266.Lattice
