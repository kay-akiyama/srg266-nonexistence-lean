/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.MultivariatePoisson
import Mathlib.Topology.ContinuousMap.Periodic

/-!
# Continuous periodization on a finite-dimensional torus

This file constructs the continuous torus periodization of a continuous
function from local normal convergence of its integral translates.  The
construction is independent of Poisson summation and of the particular
Gaussian functions used later in the rank-24 theta argument.
-/

noncomputable section

namespace SRG266.Lattice

open scoped FourierTransform

/-- Translation of a continuous function by an integral coordinate vector. -/
def integerTranslate {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (z : Fin n → ℤ) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  f.comp (ContinuousMap.addRight (intVectorToReal z))

@[simp]
theorem integerTranslate_apply {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (z : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    integerTranslate f z x = f (x + intVectorToReal z) :=
  rfl

@[simp]
theorem intVectorToReal_add {n : ℕ} (a b : Fin n → ℤ) :
    intVectorToReal (a + b) = intVectorToReal a + intVectorToReal b := by
  ext i
  simp [intVectorToReal]

@[simp]
theorem intVectorToReal_zero {n : ℕ} :
    intVectorToReal (0 : Fin n → ℤ) = 0 := by
  ext i
  simp [intVectorToReal]

/-- Local normal convergence of all integral translates.  This is the exact
convergence estimate needed to construct a continuous periodization. -/
abbrev LocallyNormallySummableIntegerTranslates {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)),
    Summable fun z : Fin n → ℤ => ‖(integerTranslate f z).restrict K‖

/-- The locally uniformly convergent sum of all integral translates. -/
def integerTranslateSum {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  ∑' z : Fin n → ℤ, integerTranslate f z

theorem integerTranslateSum_apply {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (x : EuclideanSpace ℝ (Fin n)) :
    integerTranslateSum f x =
      ∑' z : Fin n → ℤ, f (x + intVectorToReal z) := by
  let hs : Summable fun z : Fin n → ℤ => integerTranslate f z :=
    ContinuousMap.summable_of_locally_summable_norm hf
  exact (ContinuousMap.tsum_apply hs x).symm

/-- The translate sum is invariant under every integral coordinate shift. -/
theorem integerTranslateSum_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (x : EuclideanSpace ℝ (Fin n)) (a : Fin n → ℤ) :
    integerTranslateSum f (x + intVectorToReal a) =
      integerTranslateSum f x := by
  rw [integerTranslateSum_apply f hf, integerTranslateSum_apply f hf]
  rw [← (Equiv.addRight a).tsum_eq
    (fun z : Fin n → ℤ => f (x + intVectorToReal z))]
  congr 1
  funext z
  simp only [Equiv.coe_addRight, intVectorToReal_add]
  congr 1
  abel

/-- The coordinate quotient map from Euclidean space to the unit torus. -/
def euclideanToUnitTorus {n : ℕ} :
    C(EuclideanSpace ℝ (Fin n), UnitAddTorus (Fin n)) where
  toFun x := fun i => (x i : UnitAddCircle)
  continuous_toFun := by fun_prop

/-- The coordinate quotient map is an open quotient map. -/
theorem euclideanToUnitTorus_isOpenQuotientMap {n : ℕ} :
    IsOpenQuotientMap (@euclideanToUnitTorus n) := by
  let hPi : IsOpenQuotientMap
      (Pi.map fun _ : Fin n => ((↑) : ℝ → UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ =>
      QuotientAddGroup.isOpenQuotientMap_mk
  let hLp := (PiLp.homeomorph 2 fun _ : Fin n => ℝ).isOpenQuotientMap
  exact hPi.comp hLp

/-- Two Euclidean vectors with the same torus image differ by an integral
coordinate vector. -/
theorem exists_intVector_add_eq_of_euclideanToUnitTorus_eq {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : euclideanToUnitTorus x = euclideanToUnitTorus y) :
    ∃ z : Fin n → ℤ, x + intVectorToReal z = y := by
  have hcoord : ∀ i : Fin n, ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
    intro i
    have hi := congrFun hxy i
    change (↑(x i) : UnitAddCircle) = (↑(y i) : UnitAddCircle) at hi
    change (↑(y i - x i) : UnitAddCircle) = 0
    rw [QuotientAddGroup.mk_sub, hi, sub_self]
  choose z hz using fun i => (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hcoord i)
  refine ⟨z, ?_⟩
  ext i
  have hzi : (z i : ℝ) = y i - x i := by
    simpa using hz i
  simp only [PiLp.add_apply, intVectorToReal]
  rw [hzi]
  abel

/-- Continuous periodization on `ℝ^n / ℤ^n`, constructed by descent along
the coordinate quotient map. -/
def torusPeriodization {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f) :
    C(UnitAddTorus (Fin n), ℂ) :=
  euclideanToUnitTorus_isOpenQuotientMap.isQuotientMap.lift
    (integerTranslateSum f) fun x y hxy => by
      obtain ⟨z, hz⟩ :=
        exists_intVector_add_eq_of_euclideanToUnitTorus_eq hxy
      rw [← hz, integerTranslateSum_add_int f hf]

@[simp]
theorem torusPeriodization_euclideanToUnitTorus {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (x : EuclideanSpace ℝ (Fin n)) :
    torusPeriodization f hf (euclideanToUnitTorus x) =
      ∑' z : Fin n → ℤ, f (x + intVectorToReal z) := by
  change (torusPeriodization f hf).comp euclideanToUnitTorus x = _
  rw [torusPeriodization,
    Topology.IsQuotientMap.lift_comp, integerTranslateSum_apply f hf]

theorem torusPeriodization_zero {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f) :
    torusPeriodization f hf 0 =
      ∑' z : Fin n → ℤ, f (intVectorToReal z) := by
  calc
    torusPeriodization f hf 0 =
        torusPeriodization f hf (euclideanToUnitTorus 0) := by
      congr 1
    _ = ∑' z : Fin n → ℤ, f (0 + intVectorToReal z) :=
      torusPeriodization_euclideanToUnitTorus f hf 0
    _ = ∑' z : Fin n → ℤ, f (intVectorToReal z) := by simp only [zero_add]

/-- Local normal convergence already implies absolute convergence of the
values on the integral lattice. -/
theorem summable_integerValues_of_locallyNormal {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f) :
    Summable fun z : Fin n → ℤ => f (intVectorToReal z) := by
  apply Summable.of_norm
  have h := hf ({0} : TopologicalSpace.Compacts
    (EuclideanSpace ℝ (Fin n)))
  convert h using 1
  funext z
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp [integerTranslate]

/-- Package the constructed periodization as Poisson data once its Fourier
coefficient identity and dual summability have been established. -/
def piPoissonPeriodizationData_of_locallyNormal {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (hcoeff : ∀ m : Fin n → ℤ,
      UnitAddTorus.mFourierCoeff (torusPeriodization f hf) m =
        𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m))
    (hdual : Summable fun m : Fin n → ℤ =>
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m)) :
    PiPoissonPeriodizationData
      (f : EuclideanSpace ℝ (Fin n) → ℂ) where
  periodization := torusPeriodization f hf
  periodization_zero := torusPeriodization_zero f hf
  fourierCoeff := hcoeff
  latticeSummable := summable_integerValues_of_locallyNormal f hf
  fourierSummable := hdual

end SRG266.Lattice
