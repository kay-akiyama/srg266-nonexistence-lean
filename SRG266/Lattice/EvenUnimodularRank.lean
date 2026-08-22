/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ComplexGaussianLatticePoisson

/-!
# Rank divisibility of positive-definite even unimodular lattices

The scalar theta sum is periodic under translation of its right-half-plane
parameter by `i` when all lattice norms are even.  Complex Gaussian Poisson
summation supplies inversion.  Applying these two identities around the
standard five-step modular cycle based at `1` forces the rank to be divisible
by eight.
-/

noncomputable section

namespace SRG266.Lattice

open scoped RealInnerProductSpace

/-- Scalar theta sum in the open right half-plane. -/
def latticeGaussianTheta {n : ℕ} (L : PDUnimodularLattice n) (z : ℂ) : ℂ :=
  ∑' m : Fin n → ℤ,
    complexGaussian z (pdEuclideanEquiv L (intVectorToReal m))

/-- Poisson inversion for the scalar lattice theta sum. -/
theorem latticeGaussianTheta_inv {n : ℕ} (L : PDUnimodularLattice n)
    {z : ℂ} (hz : 0 < z.re) :
    latticeGaussianTheta L z⁻¹ =
      z ^ ((n : ℂ) / 2) * latticeGaussianTheta L z := by
  have hp := complexGaussian_latticePoisson L hz
  change latticeGaussianTheta L z =
    ((Real.pi : ℂ) / ((Real.pi : ℂ) * z)) ^ ((n : ℂ) / 2) *
      latticeGaussianTheta L z⁻¹ at hp
  have hz0 : z ≠ 0 := fun h => by simpa [h] using hz.ne'
  have harg : z.arg ≠ Real.pi := by
    rw [ne_eq, Complex.arg_eq_pi_iff]
    exact fun h => (not_lt_of_ge hz.le) h.1
  have hbase : (Real.pi : ℂ) / ((Real.pi : ℂ) * z) = z⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, hz0]
  rw [hbase, Complex.inv_cpow z ((n : ℂ) / 2) harg] at hp
  have hpow0 : z ^ ((n : ℂ) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  calc
    latticeGaussianTheta L z⁻¹ =
        z ^ ((n : ℂ) / 2) *
          ((z ^ ((n : ℂ) / 2))⁻¹ * latticeGaussianTheta L z⁻¹) := by
      field_simp
    _ = z ^ ((n : ℂ) / 2) * latticeGaussianTheta L z := by rw [← hp]

/-- Adding `i` to the Gaussian parameter does not change one term when its
squared norm is an even integer. -/
theorem complexGaussian_add_I_of_even_pairing {n : ℕ}
    (L : PDUnimodularLattice n)
    (heven : ∀ x : L.carrier, Even (L.pairing x x))
    (z : ℂ) (m : Fin n → ℤ) :
    complexGaussian (z + Complex.I)
        (pdEuclideanEquiv L (intVectorToReal m)) =
      complexGaussian z (pdEuclideanEquiv L (intVectorToReal m)) := by
  obtain ⟨k, hk⟩ := heven (pdCoordEquiv L m)
  have hk' : L.pairing (pdCoordEquiv L m) (pdCoordEquiv L m) = 2 * k := by
    linarith
  have hnorm :
      ‖pdEuclideanEquiv L (intVectorToReal m)‖ ^ 2 =
        ((2 * k : ℤ) : ℝ) := by
    rw [norm_sq_pdEuclideanEquiv_intVector]
    exact_mod_cast hk'
  unfold complexGaussian
  rw [show
      -((Real.pi : ℂ) * (z + Complex.I)) *
          (‖pdEuclideanEquiv L (intVectorToReal m)‖ : ℂ) ^ 2 =
        -((Real.pi : ℂ) * z) *
            (‖pdEuclideanEquiv L (intVectorToReal m)‖ : ℂ) ^ 2 +
          (-k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
    have hcast :
        (‖pdEuclideanEquiv L (intVectorToReal m)‖ : ℂ) ^ 2 =
          (((2 * k : ℤ) : ℝ) : ℂ) := by exact_mod_cast hnorm
    rw [hcast]
    push_cast
    ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The scalar theta sum of an even lattice has period `i`. -/
theorem latticeGaussianTheta_add_I {n : ℕ}
    (L : PDUnimodularLattice n)
    (heven : ∀ x : L.carrier, Even (L.pairing x x)) (z : ℂ) :
    latticeGaussianTheta L (z + Complex.I) = latticeGaussianTheta L z := by
  unfold latticeGaussianTheta
  apply tsum_congr
  exact complexGaussian_add_I_of_even_pairing L heven z

/-- The argument of `1-i` is `-pi/4`. -/
theorem arg_one_sub_I : Complex.arg (1 - Complex.I) = -(Real.pi / 4) := by
  have hpolar :
      ((Real.sqrt 2 : ℝ) : ℂ) *
          (Complex.cos ((-(Real.pi / 4) : ℝ) : ℂ) +
            Complex.sin ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) =
        1 - Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, sub_zero, mul_one, Complex.one_re,
        Complex.sub_re, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
        Complex.cos_ofReal_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, add_zero, mul_one, Complex.one_im,
        Complex.sub_im, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hpolar]
  apply Complex.arg_mul_cos_add_sin_mul_I
  · positivity
  constructor
  · have := Real.pi_pos
    linarith
  · have := Real.pi_pos
    linarith

/-- Multiplying the two Gaussian inversion factors occurring in the modular
cycle gives the expected eighth-root-of-unity phase. -/
theorem one_sub_I_cpow_cycle (n : ℕ) :
    (1 - Complex.I) ^ ((n : ℂ) / 2) *
        ((1 - Complex.I) / 2) ^ ((n : ℂ) / 2) =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (n : ℂ) / 4) := by
  let a : ℂ := 1 - Complex.I
  let b : ℂ := (1 - Complex.I) / 2
  have ha0 : a ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [a] at him
  have hb0 : b ≠ 0 := div_ne_zero ha0 (by norm_num)
  have hargA : a.arg = -(Real.pi / 4) := arg_one_sub_I
  have hargB : b.arg = -(Real.pi / 4) := by
    dsimp only [b]
    rw [div_eq_mul_inv]
    rw [show (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num]
    rw [Complex.arg_mul_real (by positivity)]
    exact arg_one_sub_I
  have hargSum : a.arg + b.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hargA, hargB]
    constructor <;> nlinarith [Real.pi_pos]
  have hlog : Complex.log (a * b) = Complex.log a + Complex.log b :=
    Complex.log_mul ha0 hb0 hargSum
  have hab : a * b = -Complex.I := by
    dsimp only [a, b]
    field_simp
    calc
      (1 - Complex.I) ^ 2 = 1 - 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = -(Complex.I * 2) := by rw [Complex.I_sq]; ring
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hb0, ← Complex.exp_add]
  rw [← add_mul, ← hlog, hab]
  have hnegI0 : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  rw [← Complex.cpow_def_of_ne_zero hnegI0]
  rw [Complex.cpow_def_of_ne_zero hnegI0]
  congr 1
  rw [Complex.log]
  simp only [norm_neg, Complex.norm_I, Real.log_one, Complex.arg_neg_I]
  push_cast
  ring

/-- The scalar theta sum at the real parameter `1` is nonzero. -/
theorem latticeGaussianTheta_one_ne_zero {n : ℕ}
    (L : PDUnimodularLattice n) : latticeGaussianTheta L 1 ≠ 0 := by
  have hsumC := summable_complexGaussian_pdEuclideanEquiv_intVector L
    (z := (1 : ℂ)) (by norm_num)
  have hsumR : Summable fun m : Fin n → ℤ =>
      (complexGaussian 1
        (pdEuclideanEquiv L (intVectorToReal m))).re :=
    Complex.reCLM.summable hsumC
  have hnonneg : ∀ m : Fin n → ℤ, 0 ≤
      (complexGaussian 1
        (pdEuclideanEquiv L (intVectorToReal m))).re := by
    intro m
    unfold complexGaussian
    rw [show -((Real.pi : ℂ) * 1) *
        (‖pdEuclideanEquiv L (intVectorToReal m)‖ : ℂ) ^ 2 =
      ((-Real.pi *
        ‖pdEuclideanEquiv L (intVectorToReal m)‖ ^ 2 : ℝ) : ℂ) by
      norm_cast
      ring]
    rw [Complex.exp_ofReal_re]
    positivity
  have hzero : 0 <
      (complexGaussian 1
        (pdEuclideanEquiv L (intVectorToReal (0 : Fin n → ℤ)))).re := by
    rw [show intVectorToReal (0 : Fin n → ℤ) = 0 by
      ext i
      simp [intVectorToReal]]
    rw [map_zero]
    simp [complexGaussian]
  have hpos := hsumR.tsum_pos hnonneg (0 : Fin n → ℤ) hzero
  intro htheta
  have hre := Complex.reCLM.map_tsum hsumC
  change (latticeGaussianTheta L 1).re =
    ∑' m : Fin n → ℤ,
      (complexGaussian 1
        (pdEuclideanEquiv L (intVectorToReal m))).re at hre
  rw [htheta] at hre
  norm_num at hre
  linarith

/-- A positive-definite even unimodular lattice has rank divisible by eight. -/
theorem eight_dvd_rank_of_even_unimodular {n : ℕ}
    (L : PDUnimodularLattice n)
    (heven : ∀ x : L.carrier, Even (L.pairing x x)) : 8 ∣ n := by
  let a : ℂ := 1 - Complex.I
  let b : ℂ := (1 - Complex.I) / 2
  have haRe : 0 < a.re := by norm_num [a]
  have hbRe : 0 < b.re := by norm_num [b]
  have haInv : a⁻¹ = (1 + Complex.I) / 2 := by
    apply Complex.ext <;>
      norm_num [a, Complex.inv_re, Complex.inv_im, Complex.normSq]
  have hbInv : b⁻¹ = 1 + Complex.I := by
    apply Complex.ext <;>
      norm_num [b, Complex.inv_re, Complex.inv_im, Complex.div_re,
        Complex.div_im, Complex.normSq]
  have hperiodA : latticeGaussianTheta L a = latticeGaussianTheta L 1 := by
    have hp := latticeGaussianTheta_add_I L heven a
    simpa only [a, sub_add_cancel] using hp.symm
  have hperiodB : latticeGaussianTheta L a⁻¹ = latticeGaussianTheta L b := by
    have hp := latticeGaussianTheta_add_I L heven b
    rw [haInv]
    calc
      latticeGaussianTheta L ((1 + Complex.I) / 2) =
          latticeGaussianTheta L (b + Complex.I) := by
            congr 1
            dsimp only [b]
            ring
      _ = latticeGaussianTheta L b := hp
  have hperiodEnd : latticeGaussianTheta L b⁻¹ = latticeGaussianTheta L 1 := by
    have hp := latticeGaussianTheta_add_I L heven 1
    rw [hbInv]
    exact hp
  have hinvA := latticeGaussianTheta_inv L haRe
  have hinvB := latticeGaussianTheta_inv L hbRe
  rw [hperiodA, hperiodB] at hinvA
  rw [hperiodEnd] at hinvB
  have hcycle : latticeGaussianTheta L 1 =
      (1 - Complex.I) ^ ((n : ℂ) / 2) *
        ((1 - Complex.I) / 2) ^ ((n : ℂ) / 2) *
          latticeGaussianTheta L 1 := by
    calc
      latticeGaussianTheta L 1 =
          b ^ ((n : ℂ) / 2) * latticeGaussianTheta L b := hinvB
      _ = b ^ ((n : ℂ) / 2) *
          (a ^ ((n : ℂ) / 2) * latticeGaussianTheta L 1) := by rw [hinvA]
      _ = (1 - Complex.I) ^ ((n : ℂ) / 2) *
          ((1 - Complex.I) / 2) ^ ((n : ℂ) / 2) *
            latticeGaussianTheta L 1 := by dsimp only [a, b]; ring
  have htheta0 := latticeGaussianTheta_one_ne_zero L
  have hphase : Complex.exp
      (-(Real.pi : ℂ) * Complex.I * (n : ℂ) / 4) = 1 := by
    rw [← one_sub_I_cpow_cycle]
    apply mul_right_cancel₀ htheta0
    simpa only [one_mul] using hcycle.symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hphase
  have hk' :
      -((Real.pi * (n : ℝ) / 4 : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
    calc
      -((Real.pi * (n : ℝ) / 4 : ℝ) : ℂ) * Complex.I =
          -(Real.pi : ℂ) * Complex.I * (n : ℂ) / 4 := by
            push_cast
            ring
      _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
      _ = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
  have him := congrArg Complex.im hk'
  simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_mul, mul_one,
    add_zero] at him
  norm_num [Complex.neg_re] at him
  have hdvdZ : (8 : ℤ) ∣ (n : ℤ) := by
    refine ⟨-k, ?_⟩
    have hnreal : (n : ℝ) = -8 * (k : ℝ) := by
      nlinarith [Real.pi_pos]
    have hnint : (n : ℤ) = -8 * k := by exact_mod_cast hnreal
    calc
      (n : ℤ) = -8 * k := hnint
      _ = 8 * -k := by ring
  exact_mod_cast hdvdZ

end SRG266.Lattice
