/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.SchwartzLocalNormal
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Poisson summation for Euclidean Schwartz functions

This file performs the remaining fundamental-domain calculation for the
continuous periodization constructed in `SchwartzPeriodization.lean`.
-/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The half-open unit cube used by the torus Fourier-coefficient formula. -/
def standardCubeIoc (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- The `Ioc` cube and Mathlib's standard `Ico` lattice fundamental domain
agree almost everywhere. -/
theorem standardCubeIoc_ae_eq_fundamentalDomain (n : ℕ) :
    standardCubeIoc n =ᵐ[volume]
      ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)) := by
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hcube : standardCubeIoc n =
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [standardCubeIoc]
  rw [hcube]
  exact Measure.pi_Ioc_ae_eq_pi_Icc.trans Measure.pi_Ico_ae_eq_pi_Icc.symm

/-- The half-open unit cube has volume one. -/
@[simp]
theorem volume_standardCubeIoc (n : ℕ) :
    volume (standardCubeIoc n) = 1 := by
  have hcube : standardCubeIoc n =
      Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [standardCubeIoc]
  rw [hcube, Real.volume_pi_Ioc]
  simp

/-- The closed unit cube in Euclidean coordinates. -/
def closedUnitCubeEuclidean (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

theorem isCompact_closedUnitCubeEuclidean (n : ℕ) :
    IsCompact (closedUnitCubeEuclidean n) := by
  have hcoord : IsCompact
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ ↦ isCompact_Icc
  have hpre :=
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isCompact_preimage.mpr hcoord
  convert hpre using 1
  ext x
  rfl

/-- Integral translation is invisible on the coordinate torus. -/
theorem mFourier_add_int {n : ℕ} (a m : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier m
        (fun i ↦ (((a i : ℝ) + x i : ℝ) : UnitAddCircle)) =
      UnitAddTorus.mFourier m (fun i ↦ (x i : UnitAddCircle)) := by
  congr 1
  funext i
  simp

/-- Integral coordinate vectors, regarded as elements of the additive group
underlying the standard coordinate lattice. -/
def intVectorEquivStandardIntegerAddSubgroup (n : ℕ) :
    (Fin n → ℤ) ≃ (standardIntegerLattice n).toAddSubgroup :=
  (intVectorEquivStandardIntegerLattice n).toEquiv.trans
    { toFun := fun v ↦ ⟨v, v.property⟩
      invFun := fun v ↦ ⟨v, v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

@[simp]
theorem coe_intVectorEquivStandardIntegerAddSubgroup {n : ℕ} (z : Fin n → ℤ) :
    ((intVectorEquivStandardIntegerAddSubgroup n z :
      (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) =
        fun i ↦ (z i : ℝ) := by
  exact coe_intVectorEquivStandardIntegerLattice z

/-- The torus monomial at a real representative is the Euclidean Fourier
kernel at the corresponding integral frequency. -/
theorem mFourier_neg_eq_fourierChar_inner {n : ℕ}
    (m : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) =
      (𝐞 (-inner ℝ (WithLp.toLp 2 x) (intVectorToReal m)) : Circle) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
    PiLp.inner_apply, intVectorToReal]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- The coordinate form of the Euclidean Fourier integrand. -/
def coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    (Fin n → ℝ) → ℂ := fun x =>
  UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
    f (WithLp.toLp 2 x)

theorem coordinatePoissonKernel_continuous {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    Continuous (coordinatePoissonKernel f m) := by
  unfold coordinatePoissonKernel
  fun_prop

theorem coordinatePoissonKernel_integrable {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hf : Integrable f)
    (m : Fin n → ℤ) :
    Integrable (coordinatePoissonKernel f m) := by
  have hfun : coordinatePoissonKernel f m =
      (fun y : EuclideanSpace ℝ (Fin n) =>
        𝐞 (-inner ℝ y (intVectorToReal m)) • f y) ∘ WithLp.toLp 2 := by
    funext x
    rw [coordinatePoissonKernel, Function.comp_apply,
      mFourier_neg_eq_fourierChar_inner]
    rfl
  rw [hfun]
  apply (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable
  exact (Real.fourierIntegral_convergent_iff (intVectorToReal m)).2 hf

/-- The integrals of the norms of all translated Fourier kernels over the
unit cube form a summable family.  Local normal convergence supplies the
uniform majorant; no interchange of an unverified series is used here. -/
theorem summable_cube_integral_norm_coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (m : Fin n → ℤ) :
    Summable fun z : Fin n → ℤ ↦
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖ := by
  let K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)) :=
    ⟨closedUnitCubeEuclidean n, isCompact_closedUnitCubeEuclidean n⟩
  have hsup : Summable fun z : Fin n → ℤ ↦
      ‖(integerTranslate f z).restrict K‖ := hf K
  refine Summable.of_nonneg_of_le (fun z ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun z ↦ ?_)
    hsup
  have hnonneg : 0 ≤
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  calc
    (∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖) =
        ‖∫ x : Fin n → ℝ in standardCubeIoc n,
          ‖coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x)‖‖ :=
      (Real.norm_of_nonneg hnonneg).symm
    _ ≤ ‖(integerTranslate f z).restrict K‖ *
        volume.real (standardCubeIoc n) := by
      apply norm_setIntegral_le_of_norm_le_const
      · simp
      · intro x hx
        have hvec :
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) =
              fun i ↦ (z i : ℝ) + x i := by
          funext i
          rw [coe_intVectorEquivStandardIntegerLattice]
          rfl
        rw [Real.norm_of_nonneg (norm_nonneg _), hvec,
          coordinatePoissonKernel, norm_smul, mFourier_add_int]
        have hphase :
            ‖UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle))‖ = 1 := by
          rw [mFourier_neg_eq_fourierChar_inner]
          exact Circle.norm_coe _
        rw [hphase, one_mul]
        have hxK : WithLp.toLp 2 x ∈ closedUnitCubeEuclidean n := by
          intro i
          exact ⟨le_of_lt (hx i).1, (hx i).2⟩
        have hbound := ContinuousMap.norm_coe_le_norm
          ((integerTranslate f z).restrict K) ⟨WithLp.toLp 2 x, hxK⟩
        change ‖f (WithLp.toLp 2 x + intVectorToReal z)‖ ≤
          ‖(integerTranslate f z).restrict K‖ at hbound
        calc
          ‖f (WithLp.toLp 2 fun i ↦ (z i : ℝ) + x i)‖ =
              ‖f (WithLp.toLp 2 x + intVectorToReal z)‖ := by
            congr 2
            ext i
            simp [intVectorToReal, add_comm]
          _ ≤ ‖(integerTranslate f z).restrict K‖ := hbound
    _ = ‖(integerTranslate f z).restrict K‖ := by
      simp [measureReal_def, volume_standardCubeIoc]

/-- Tiling coordinate space by the standard integral lattice rewrites the
full Fourier integral as a sum of integrals over the half-open unit cube. -/
theorem integral_coordinatePoissonKernel_eq_tsum_cube {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hf : Integrable f)
    (m : Fin n → ℤ) :
    (∫ x : Fin n → ℝ, coordinatePoissonKernel f m x) =
      ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) := by
  letI : Countable (standardIntegerLattice n).toAddSubgroup := by
    change Countable (standardIntegerLattice n)
    infer_instance
  have hfd :=
    (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume).integral_eq_tsum''
      (coordinatePoissonKernel f m) (coordinatePoissonKernel_integrable f hf m)
  calc
    (∫ x : Fin n → ℝ, coordinatePoissonKernel f m x) =
        ∑' v : (standardIntegerLattice n).toAddSubgroup,
          ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
          coordinatePoissonKernel f m (v + x) := by
      simpa only [AddSubgroup.vadd_def, vadd_eq_add] using hfd
    _ = ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerAddSubgroup n z :
              (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) + x) := by
      exact ((intVectorEquivStandardIntegerAddSubgroup n).tsum_eq
          (fun v : (standardIntegerLattice n).toAddSubgroup ↦
            ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
              coordinatePoissonKernel f m (v + x))).symm
    _ = ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerAddSubgroup n z :
              (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) + x) := by
      apply tsum_congr
      intro z
      apply setIntegral_congr_set
      exact (standardCubeIoc_ae_eq_fundamentalDomain n).symm
    _ = _ := by
      simp only [coe_intVectorEquivStandardIntegerAddSubgroup,
        coe_intVectorEquivStandardIntegerLattice]

/-- Absolute convergence justifies exchanging the integral over the unit
cube with the sum of all integral translates. -/
theorem tsum_cube_integral_coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (m : Fin n → ℤ) :
    (∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x)) =
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ∑' z : Fin n → ℤ,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) := by
  apply MeasureTheory.integral_tsum_of_summable_integral_norm
  · intro z
    have hcont : Continuous fun x : Fin n → ℝ ↦
        coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x) := by
      exact (coordinatePoissonKernel_continuous f m).comp (by fun_prop)
    have hcompact : IsCompact
        {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} :=
      isCompact_pi_infinite fun _ ↦ isCompact_Icc
    apply (hcont.continuousOn.integrableOn_compact hcompact).mono_set
    intro x hx i
    exact ⟨le_of_lt (hx i).1, (hx i).2⟩
  · exact summable_cube_integral_norm_coordinatePoissonKernel f hf m

/-- On an integral translate, the torus monomial is unchanged and only the
Schwartz factor is translated. -/
theorem coordinatePoissonKernel_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (m z : Fin n → ℤ) (x : Fin n → ℝ) :
    coordinatePoissonKernel f m
        (((intVectorEquivStandardIntegerLattice n z :
          standardIntegerLattice n) : Fin n → ℝ) + x) =
      UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
        f (WithLp.toLp 2 x + intVectorToReal z) := by
  have hvec :
      (((intVectorEquivStandardIntegerLattice n z :
        standardIntegerLattice n) : Fin n → ℝ) + x) =
        fun i ↦ (z i : ℝ) + x i := by
    funext i
    rw [coe_intVectorEquivStandardIntegerLattice]
    rfl
  rw [hvec, coordinatePoissonKernel, mFourier_add_int]
  congr 2
  ext i
  simp [intVectorToReal, add_comm]

/-- Pointwise, the translated-kernel sum is the torus monomial times the
ordinary periodization. -/
theorem tsum_coordinatePoissonKernel_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (m : Fin n → ℤ) (x : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
      coordinatePoissonKernel f m
        (((intVectorEquivStandardIntegerLattice n z :
          standardIntegerLattice n) : Fin n → ℝ) + x)) =
      UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
        ∑' z : Fin n → ℤ, f (WithLp.toLp 2 x + intVectorToReal z) := by
  rw [tsum_congr fun z ↦ coordinatePoissonKernel_add_int f m z x]
  exact tsum_const_smul'' _

/-- After passing from coordinate functions to Euclidean space, the full
Fourier kernel integral is Mathlib's Euclidean Fourier transform. -/
theorem integral_mFourier_kernel_eq_fourier {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    (∫ x : Fin n → ℝ,
      UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
        f (WithLp.toLp 2 x)) =
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) := by
  rw [Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  rw [mFourier_neg_eq_fourierChar_inner]
  rfl

/-- The Fourier coefficients of a locally normally convergent continuous
periodization are the Euclidean Fourier transform at integral frequencies. -/
theorem torusPeriodization_mFourierCoeff {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hfint : Integrable f)
    (hflocal : LocallyNormallySummableIntegerTranslates f)
    (m : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodization f hflocal) m =
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ m (0 : Fin n → ℝ)]
  simp only [Pi.zero_apply, zero_add]
  change (∫ x : Fin n → ℝ in standardCubeIoc n,
        UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
        torusPeriodization f hflocal
          (fun i ↦ (x i : UnitAddCircle))) = _
  calc
    (∫ x : Fin n → ℝ in standardCubeIoc n,
          UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
          torusPeriodization f hflocal
            (fun i ↦ (x i : UnitAddCircle))) =
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          ∑' z : Fin n → ℤ,
            coordinatePoissonKernel f m
              (((intVectorEquivStandardIntegerLattice n z :
                standardIntegerLattice n) : Fin n → ℝ) + x) := by
      apply integral_congr_ae
      filter_upwards with x
      change UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
          torusPeriodization f hflocal
            (euclideanToUnitTorus (WithLp.toLp 2 x)) = _
      rw [torusPeriodization_euclideanToUnitTorus]
      exact (tsum_coordinatePoissonKernel_add_int f m x).symm
    _ = ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) :=
      (tsum_cube_integral_coordinatePoissonKernel f hflocal m).symm
    _ = ∫ x : Fin n → ℝ, coordinatePoissonKernel f m x :=
      (integral_coordinatePoissonKernel_eq_tsum_cube f hfint m).symm
    _ = 𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) :=
      integral_mFourier_kernel_eq_fourier f m

/-- Poisson periodization data for a continuous integrable function with
locally normal integral translates and a summable Fourier restriction. -/
def continuousPiPoissonPeriodizationData {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hfint : Integrable f)
    (hflocal : LocallyNormallySummableIntegerTranslates f)
    (hfdual : Summable fun m : Fin n → ℤ =>
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m)) :
    PiPoissonPeriodizationData
      (f : EuclideanSpace ℝ (Fin n) → ℂ) :=
  piPoissonPeriodizationData_of_locallyNormal f hflocal
    (torusPeriodization_mFourierCoeff f hfint hflocal) hfdual

/-- **Multivariate Poisson summation without a Schwartz-space wrapper.**
The analytic hypotheses expose exactly what periodization uses. -/
theorem continuous_piPoisson {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hfint : Integrable f)
    (hflocal : LocallyNormallySummableIntegerTranslates f)
    (hfdual : Summable fun m : Fin n → ℤ =>
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m)) :
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
      ∑' m : Fin n → ℤ,
        𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) :=
  piPoisson_of_periodization
    (continuousPiPoissonPeriodizationData f hfint hflocal hfdual)

/-- The fully checked periodization package for any Euclidean Schwartz
function. -/
def schwartzPiPoissonPeriodizationData {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    PiPoissonPeriodizationData
      (f : EuclideanSpace ℝ (Fin n) → ℂ) :=
  continuousPiPoissonPeriodizationData
    (⟨f, f.continuous⟩ : C(EuclideanSpace ℝ (Fin n), ℂ)) f.integrable
    (SRG266.Lattice.SchwartzMap.locallyNormallySummableIntegerTranslates f)
    (SRG266.Lattice.SchwartzMap.summable_fourier_intVector f)

/-- **Multivariate Poisson summation for Euclidean Schwartz functions.** -/
theorem schwartz_piPoisson {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    (∑' z : Fin n → ℤ, f (intVectorToReal z)) =
      ∑' m : Fin n → ℤ,
        𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) :=
  piPoisson_of_periodization (schwartzPiPoissonPeriodizationData f)

end SRG266.Lattice
