/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HarmonicGaussian
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The Hessian of a radial Gaussian

This file computes the first two Fréchet derivatives of

`w ↦ exp (q * ‖w‖²)`

on a real inner-product space.  The second-derivative formula is the
analytic calculation used to turn multiplication by a quadratic polynomial
before Fourier transform into a trace-free Hessian afterwards.
-/

noncomputable section

namespace SRG266.Lattice

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A radial complex Gaussian with arbitrary complex rate. -/
def radialExp (q : ℂ) (w : V) : ℂ :=
  Complex.exp (q * (‖w‖ ^ 2 : ℝ))

theorem hasFDerivAt_radialExp (q : ℂ) (w : V) :
    HasFDerivAt (radialExp q)
      (Complex.exp (q * (‖w‖ ^ 2 : ℝ)) •
        (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ w)))) w := by
  unfold radialExp
  apply HasFDerivAt.cexp
  apply HasFDerivAt.const_mul
  exact Complex.ofRealCLM.hasFDerivAt.comp w
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt

theorem fderiv_radialExp_apply (q : ℂ) (w x : V) :
    fderiv ℝ (radialExp q) w x =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) * q * (2 * inner ℝ w x) := by
  rw [(hasFDerivAt_radialExp q w).fderiv]
  simp [mul_assoc]

/-- The first directional derivative of `radialExp`, retained as a named
function so that its derivative can be computed independently. -/
def radialExpFirst (q : ℂ) (y z : V) : ℂ :=
  radialExp q z * q * ((2 * inner ℝ z y : ℝ) : ℂ)

theorem hasFDerivAt_radialExpFirst (q : ℂ) (y w : V) :
    HasFDerivAt (radialExpFirst q y)
      (radialExp q w •
          (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))) +
        (q * ((2 * inner ℝ w y : ℝ) : ℂ)) •
          (Complex.exp (q * (‖w‖ ^ 2 : ℝ)) •
            (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ w))))) w := by
  unfold radialExpFirst
  have hlin : HasFDerivAt (fun z : V => q * (2 * inner ℝ z y : ℝ))
      (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))) w := by
    convert (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))).hasFDerivAt using 1
    ext z
    simp [real_inner_comm]
  apply ((hasFDerivAt_radialExp q w).mul hlin).congr_of_eventuallyEq
  filter_upwards with z
  simp only [Pi.mul_apply]
  ring

theorem fderiv_radialExpFirst_apply (q : ℂ) (y w x : V) :
    fderiv ℝ (radialExpFirst q y) w x =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) *
        (4 * q ^ 2 * inner ℝ w x * inner ℝ w y +
          2 * q * inner ℝ x y) := by
  rw [(hasFDerivAt_radialExpFirst q y w).fderiv]
  simp [radialExp, real_inner_comm]
  ring

/-- The Hessian of a radial Gaussian, evaluated in two directions. -/
theorem iteratedFDeriv_two_radialExp_apply (q : ℂ) (w x y : V) :
    iteratedFDeriv ℝ 2 (radialExp q) w ![x, y] =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) *
        (4 * q ^ 2 * inner ℝ w x * inner ℝ w y +
          2 * q * inner ℝ x y) := by
  rw [iteratedFDeriv_two_apply]
  have hsmooth : ContDiff ℝ ⊤ (radialExp q : V → ℂ) := by
    unfold radialExp
    have hnorm : ContDiff ℝ ⊤ (fun w : V => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
    exact Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hnorm))
  have hc : DifferentiableAt ℝ (fderiv ℝ (radialExp q : V → ℂ)) w :=
    ((hsmooth.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)) w
  have happ :
      fderiv ℝ (fun z : V => fderiv ℝ (radialExp q) z y) w x =
        fderiv ℝ (fderiv ℝ (radialExp q)) w x y := by
    rw [fderiv_clm_apply hc (differentiableAt_const (c := y))]
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at *
  rw [← happ]
  have heq : (fun z : V => fderiv ℝ (radialExp q) z y) = radialExpFirst q y := by
    funext z
    simpa [radialExpFirst, radialExp] using fderiv_radialExp_apply q z y
  rw [heq, fderiv_radialExpFirst_apply]

end SRG266.Lattice
