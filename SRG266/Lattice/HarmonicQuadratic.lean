/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The degree-two harmonic quadratic

This file isolates the trace-free quadratic polynomial used in the rank-24
weighted theta series.  For a finite-dimensional real inner-product space
`V`, it is

`dim(V) * <v,x> * <v,y> - <x,y> * <v,v>`.

The main theorem proves that its trace in every orthonormal basis is zero.
This is the finite-dimensional algebraic cancellation responsible for the
clean Fourier transform of the harmonic Gaussian.
-/

noncomputable section

namespace SRG266.Lattice

open scoped RealInnerProductSpace BigOperators

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The polarized degree-two harmonic quadratic attached to `x` and `y`. -/
def harmonicQuadratic (x y v : V) : ℝ :=
  (Module.finrank ℝ V : ℝ) * inner ℝ v x * inner ℝ v y -
    inner ℝ x y * inner ℝ v v

omit [FiniteDimensional ℝ V] in
@[simp]
theorem harmonicQuadratic_zero_left (x y : V) :
    harmonicQuadratic x y 0 = 0 := by
  simp [harmonicQuadratic]

omit [FiniteDimensional ℝ V] in
@[simp]
theorem harmonicQuadratic_neg (x y v : V) :
    harmonicQuadratic x y (-v) = harmonicQuadratic x y v := by
  simp [harmonicQuadratic]

omit [FiniteDimensional ℝ V] in
/-- The harmonic quadratic is homogeneous of degree two in its argument. -/
theorem harmonicQuadratic_smul (a : ℝ) (x y v : V) :
    harmonicQuadratic x y (a • v) = a ^ 2 * harmonicQuadratic x y v := by
  simp only [harmonicQuadratic, real_inner_smul_left, real_inner_smul_right]
  ring

omit [FiniteDimensional ℝ V] in
/-- The harmonic quadratic is symmetric in its two polarization vectors. -/
theorem harmonicQuadratic_comm (x y v : V) :
    harmonicQuadratic x y v = harmonicQuadratic y x v := by
  simp only [harmonicQuadratic, real_inner_comm x y]
  ring

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The quadratic is natural under real linear isometries. -/
theorem harmonicQuadratic_map
    (e : V ≃ₗᵢ[ℝ] W) (x y v : V) :
    harmonicQuadratic (e x) (e y) (e v) = harmonicQuadratic x y v := by
  simp only [harmonicQuadratic, LinearIsometryEquiv.inner_map_map]
  rw [← e.toLinearEquiv.finrank_eq]

omit [FiniteDimensional ℝ V] in
/-- A uniform quadratic bound for the harmonic weight. -/
theorem abs_harmonicQuadratic_le (x y v : V) :
    |harmonicQuadratic x y v| ≤
      ((Module.finrank ℝ V : ℝ) + 1) * ‖x‖ * ‖y‖ * ‖v‖ ^ 2 := by
  let d : ℝ := Module.finrank ℝ V
  have hd : 0 ≤ d := by positivity
  have hvx := abs_real_inner_le_norm v x
  have hvy := abs_real_inner_le_norm v y
  have hxy := abs_real_inner_le_norm x y
  have hvv : |inner ℝ v v| = ‖v‖ * ‖v‖ := by
    rw [real_inner_self_eq_norm_mul_norm, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    |harmonicQuadratic x y v| ≤
        |d * inner ℝ v x * inner ℝ v y| +
          |inner ℝ x y * inner ℝ v v| := by
      simpa [harmonicQuadratic, d] using
        abs_sub (d * inner ℝ v x * inner ℝ v y)
          (inner ℝ x y * inner ℝ v v)
    _ = d * |inner ℝ v x| * |inner ℝ v y| +
        |inner ℝ x y| * (‖v‖ * ‖v‖) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hd, hvv]
    _ ≤ d * (‖v‖ * ‖x‖) * (‖v‖ * ‖y‖) +
        (‖x‖ * ‖y‖) * (‖v‖ * ‖v‖) := by
      gcongr
    _ = ((Module.finrank ℝ V : ℝ) + 1) * ‖x‖ * ‖y‖ * ‖v‖ ^ 2 := by
      dsimp only [d]
      ring

omit [FiniteDimensional ℝ V] in
/-- Parseval's identity in the form needed for the trace calculation. -/
theorem sum_orthonormalBasis_inner_mul_inner
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (x y : V) :
    ∑ i, inner ℝ (b i) x * inner ℝ (b i) y = inner ℝ x y := by
  have h := b.repr.inner_map_map x y
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    OrthonormalBasis.repr_apply_apply, mul_comm] using h

omit [FiniteDimensional ℝ V] in
/-- **Harmonicity.**  The trace of `harmonicQuadratic x y` in every
orthonormal basis is zero. -/
theorem sum_harmonicQuadratic_orthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (x y : V) :
    ∑ i, harmonicQuadratic x y (b i) = 0 := by
  simp only [harmonicQuadratic, Finset.sum_sub_distrib]
  have hfirst :
      (∑ i, (Module.finrank ℝ V : ℝ) * inner ℝ (b i) x *
        inner ℝ (b i) y) =
        (Module.finrank ℝ V : ℝ) * inner ℝ x y := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, sum_orthonormalBasis_inner_mul_inner b x y]
  have hself : ∀ i, inner ℝ (b i) (b i) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hsecond :
      (∑ i, inner ℝ x y * inner ℝ (b i) (b i)) =
        (Module.finrank ℝ V : ℝ) * inner ℝ x y := by
    simp_rw [hself]
    rw [Finset.sum_const, Finset.card_univ,
      ← Module.finrank_eq_card_basis b.toBasis]
    simp only [nsmul_eq_mul]
    ring
  rw [hfirst, hsecond]
  ring

end SRG266.Lattice
