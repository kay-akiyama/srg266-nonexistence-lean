/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# A multivariate Poisson endpoint from periodization

Mathlib already proves pointwise convergence of a continuous function's
Fourier series on a finite-dimensional unit torus when its Fourier
coefficients are summable.  Consequently a multivariate Poisson formula does
not require a second Fourier-series development.  It is enough to construct
the continuous periodization of `f`, identify its value at zero, and compute
its Fourier coefficients as the Euclidean Fourier transform of `f`.

`PiPoissonPeriodizationData` records exactly those analytic facts.  The
theorem `piPoisson_of_periodization` below is the remaining formal Fourier
series argument.
-/

noncomputable section

namespace SRG266.Lattice

open scoped FourierTransform RealInnerProductSpace SchwartzMap

open Filter Asymptotics

/-- Restricting a Schwartz function to any integral lattice gives an
absolutely summable family.  This is the convergence input needed on both
sides of Poisson summation. -/
theorem SchwartzMap.summable_zlattice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) : Summable fun z : L => f z := by
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by
    dsimp only [r]
    linarith
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete E _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have htend : Tendsto ((↑) : L → E) cofinite (cocompact E) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete DiscreteTopology.isDiscrete
  exact summable_of_isBigO (ZLattice.summable_norm_rpow L r hr)
    ((f.isBigO_cocompact_rpow r).comp_tendsto htend)

/-- Coordinatewise embedding of an integral vector into real Euclidean
space. -/
def intVectorToReal {n : ℕ} (z : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => z i

/-- Coordinatewise projection of real Euclidean space to the unit torus. -/
def realVectorToUnitTorus {n : ℕ} (x : Fin n → ℝ) :
    UnitAddTorus (Fin n) :=
  fun i => (x i : UnitAddCircle)

/-- The exact data needed to deduce multivariate Poisson summation from
Mathlib's Fourier-series theorem on the unit torus. -/
structure PiPoissonPeriodizationData {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ) where
  /-- Continuous periodization of `f` on `ℝ^n / ℤ^n`. -/
  periodization : C(UnitAddTorus (Fin n), ℂ)
  /-- The value at zero is the sum over the integer lattice. -/
  periodization_zero :
    periodization 0 = ∑' z : Fin n → ℤ, f (intVectorToReal z)
  /-- Its torus Fourier coefficients are the Euclidean Fourier transform at
  integer frequencies. -/
  fourierCoeff : ∀ m : Fin n → ℤ,
    UnitAddTorus.mFourierCoeff periodization m =
      𝓕 f (intVectorToReal m)
  /-- Absolute convergence on the lattice side. -/
  latticeSummable : Summable fun z : Fin n → ℤ => f (intVectorToReal z)
  /-- Absolute convergence of the dual Fourier values. -/
  fourierSummable : Summable fun m : Fin n → ℤ =>
    𝓕 f (intVectorToReal m)

/-- **Multivariate Poisson summation from a checked periodization.** -/
theorem piPoisson_of_periodization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (P : PiPoissonPeriodizationData f) :
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
      ∑' m : Fin n → ℤ, 𝓕 f (intVectorToReal m) := by
  have hcoeffSummable :
      Summable (UnitAddTorus.mFourierCoeff P.periodization) :=
    P.fourierSummable.congr fun m => (P.fourierCoeff m).symm
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    hcoeffSummable (0 : UnitAddTorus (Fin n))
  have hcoeffSeries :
      HasSum (UnitAddTorus.mFourierCoeff P.periodization)
        (P.periodization 0) := by
    refine hseries.congr_fun fun m => ?_
    simp [UnitAddTorus.mFourier]
  have hfourierSeries :
      HasSum (fun m : Fin n → ℤ => 𝓕 f (intVectorToReal m))
        (P.periodization 0) :=
    hcoeffSeries.congr_fun fun m => (P.fourierCoeff m).symm
  calc
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
        P.periodization 0 := P.periodization_zero.symm
    _ = ∑' m : Fin n → ℤ, 𝓕 f (intVectorToReal m) :=
      hfourierSeries.tsum_eq.symm

end SRG266.Lattice
