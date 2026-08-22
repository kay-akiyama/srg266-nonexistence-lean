/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.IntegralLattice
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Rank of the integral Gram kernel

This file transports the rank computation for the local Gram matrix from
characteristic zero back to its integral kernel.

The rational support projector has rank 12 by the same idempotent-and-trace
argument used over the reals.  The coordinatewise map from integral vectors to
rational vectors is localization at the non-zero integers.  Since localization
commutes with kernels, the integral Gram kernel and the rational Gram kernel
have the same rank.  Rational rank-nullity then gives the value 208.
-/

open scoped Matrix
open nonZeroDivisors

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The rational scalar extension of the local Gram matrix. -/
def localGramMatrixRat (x : V) :
    Matrix (SecondSubconstituent G x)
      (SecondSubconstituent G x) ℚ :=
  fun B C => localGramMatrix G x B C

/-- The rational support projector `P / 495`. -/
noncomputable def localSupportProjectorRat (x : V) :
    Matrix (SecondSubconstituent G x)
      (SecondSubconstituent G x) ℚ :=
  fun B C => (localSupportNumerator G x B C : ℚ) / 495

theorem localSupportProjectorRat_idempotent
    (hG : IsHypothetical G) (x : V) :
    localSupportProjectorRat G x * localSupportProjectorRat G x =
      localSupportProjectorRat G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localSupportNumerator G x B D : ℚ) *
            (localSupportNumerator G x D C : ℚ)) =
        ((localSupportNumerator G x *
          localSupportNumerator G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ D,
      (localSupportNumerator G x B D : ℚ) / 495 *
        ((localSupportNumerator G x D C : ℚ) / 495)) =
      (localSupportNumerator G x B C : ℚ) / 495
  calc
    (∑ D,
        (localSupportNumerator G x B D : ℚ) / 495 *
          ((localSupportNumerator G x D C : ℚ) / 495)) =
        (∑ D,
          (localSupportNumerator G x B D : ℚ) *
            (localSupportNumerator G x D C : ℚ)) / 245025 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localSupportNumerator G x *
          localSupportNumerator G x) B C : ℤ) / 245025 := by
      rw [hcast]
    _ = (localSupportNumerator G x B C : ℚ) / 495 := by
      rw [localSupportNumerator_sq_apply G hG x B C]
      push_cast
      ring

theorem localSupportProjectorRat_trace
    (hG : IsHypothetical G) (x : V) :
    (localSupportProjectorRat G x).trace = 12 := by
  rw [Matrix.trace]
  change
    (∑ B : SecondSubconstituent G x,
      (localSupportNumerator G x B B : ℚ) / 495) = 12
  have hdiag :
      ∀ B : SecondSubconstituent G x,
        localSupportNumerator G x B B = 27 := by
    intro B
    simp [localSupportNumerator, localGramMatrix_diagonal G hG x B]
  simp_rw [hdiag]
  simp [secondSubconstituent_card G hG x]
  norm_num

theorem localSupportProjectorRat_rank
    (hG : IsHypothetical G) (x : V) :
    (localSupportProjectorRat G x).rank = 12 :=
  rank_eq_nat_of_idempotent_trace
    (localSupportProjectorRat G x) 12
    (localSupportProjectorRat_idempotent G hG x)
    (localSupportProjectorRat_trace G hG x)

theorem localSupportProjectorRat_mul_localGramMatrixRat
    (hG : IsHypothetical G) (x : V) :
    localSupportProjectorRat G x * localGramMatrixRat G x =
      localGramMatrixRat G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localSupportNumerator G x B D : ℚ) *
            (localGramMatrix G x D C : ℚ)) =
        ((localSupportNumerator G x * localGramMatrix G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  have hprod :=
    congrFun
      (congrFun (localSupportNumerator_mul_localGram G hG x) B) C
  change
    (localSupportNumerator G x * localGramMatrix G x) B C =
      ((495 : ℕ) • localGramMatrix G x) B C at hprod
  rw [nsmulMatrix_apply] at hprod
  change
    (∑ D,
      (localSupportNumerator G x B D : ℚ) / 495 *
        (localGramMatrix G x D C : ℚ)) =
      (localGramMatrix G x B C : ℚ)
  calc
    (∑ D,
        (localSupportNumerator G x B D : ℚ) / 495 *
          (localGramMatrix G x D C : ℚ)) =
        (∑ D,
          (localSupportNumerator G x B D : ℚ) *
            (localGramMatrix G x D C : ℚ)) / 495 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localSupportNumerator G x *
          localGramMatrix G x) B C : ℤ) / 495 := by
      rw [hcast]
    _ = (localGramMatrix G x B C : ℚ) := by
      rw [hprod]
      push_cast
      ring

/-- A rational right factor `T` satisfying `L T = P / 495`. -/
noncomputable def localGramRankFactorRat (x : V) :
    Matrix (SecondSubconstituent G x)
      (SecondSubconstituent G x) ℚ :=
  fun B C => (localGramRankFactorNumerator G x B C : ℚ) / 7425

theorem localGramMatrixRat_mul_rankFactor
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixRat G x * localGramRankFactorRat G x =
      localSupportProjectorRat G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localGramMatrix G x B D : ℚ) *
            (localGramRankFactorNumerator G x D C : ℚ)) =
        ((localGramMatrix G x *
          localGramRankFactorNumerator G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  have hprod :=
    congrFun
      (congrFun
        (fifteen_smul_localSupportNumerator_factor G hG x) B) C
  change
    ((15 : ℕ) • localSupportNumerator G x) B C =
      (localGramMatrix G x *
        localGramRankFactorNumerator G x) B C at hprod
  rw [nsmulMatrix_apply] at hprod
  change
    (∑ D,
      (localGramMatrix G x B D : ℚ) *
        ((localGramRankFactorNumerator G x D C : ℚ) / 7425)) =
      (localSupportNumerator G x B C : ℚ) / 495
  calc
    (∑ D,
        (localGramMatrix G x B D : ℚ) *
          ((localGramRankFactorNumerator G x D C : ℚ) / 7425)) =
        (∑ D,
          (localGramMatrix G x B D : ℚ) *
            (localGramRankFactorNumerator G x D C : ℚ)) / 7425 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localGramMatrix G x *
          localGramRankFactorNumerator G x) B C : ℤ) / 7425 := by
      rw [hcast]
    _ = (localSupportNumerator G x B C : ℚ) / 495 := by
      rw [← hprod]
      push_cast
      ring

theorem localGramMatrixRat_rank
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixRat G x).rank = 12 := by
  have hleSupport :
      (localGramMatrixRat G x).rank ≤
        (localSupportProjectorRat G x).rank := by
    calc
      (localGramMatrixRat G x).rank =
          (localSupportProjectorRat G x *
            localGramMatrixRat G x).rank := by
        rw [localSupportProjectorRat_mul_localGramMatrixRat G hG x]
      _ ≤ (localSupportProjectorRat G x).rank :=
        Matrix.rank_mul_le_left _ _
  have hleGram :
      (localSupportProjectorRat G x).rank ≤
        (localGramMatrixRat G x).rank := by
    calc
      (localSupportProjectorRat G x).rank =
          (localGramMatrixRat G x *
            localGramRankFactorRat G x).rank := by
        rw [localGramMatrixRat_mul_rankFactor G hG x]
      _ ≤ (localGramMatrixRat G x).rank :=
        Matrix.rank_mul_le_left _ _
  rw [localSupportProjectorRat_rank G hG x] at hleSupport hleGram
  omega

/-- Coordinatewise inclusion of integral vectors into rational vectors. -/
def integerToRationalVectors (x : V) :
    (SecondSubconstituent G x → ℤ) →ₗ[ℤ]
      (SecondSubconstituent G x → ℚ) :=
  (Algebra.linearMap ℤ ℚ).compLeft (SecondSubconstituent G x)

local instance integerToRationalVectors_isLocalized (x : V) :
    IsLocalizedModule ℤ⁰ (integerToRationalVectors G x) := by
  let f : ℤ →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ
  change IsLocalizedModule ℤ⁰
    (f.compLeft (SecondSubconstituent G x))
  change IsLocalizedModule ℤ⁰
    (LinearMap.pi fun i : SecondSubconstituent G x =>
      f.comp (LinearMap.proj (R := ℤ) i))
  infer_instance

/-- The integral Gram endomorphism transported to rational coordinate
vectors by localization. -/
noncomputable def localizedIntegralGramMap (x : V) :
    (SecondSubconstituent G x → ℚ) →ₗ[ℤ]
      (SecondSubconstituent G x → ℚ) :=
  IsLocalizedModule.map ℤ⁰
    (integerToRationalVectors G x)
    (integerToRationalVectors G x)
    (localGramMatrix G x).mulVecLin

theorem localizedIntegralGramMap_eq_localGramMatrixRat
    (x : V) :
    (localizedIntegralGramMap G x).extendScalarsOfIsLocalization ℤ⁰ ℚ =
      (localGramMatrixRat G x).mulVecLin := by
  apply LinearMap.restrictScalars_injective ℤ
  apply IsLocalizedModule.linearMap_ext ℤ⁰
    (integerToRationalVectors G x)
    (integerToRationalVectors G x)
  apply LinearMap.ext
  intro z
  ext B
  change
    (localizedIntegralGramMap G x)
        (integerToRationalVectors G x z) B =
      ∑ C,
        localGramMatrixRat G x B C *
          integerToRationalVectors G x z C
  rw [localizedIntegralGramMap]
  rw [IsLocalizedModule.map_apply]
  change
    ((∑ C, localGramMatrix G x B C * z C : ℤ) : ℚ) =
      ∑ C, (localGramMatrix G x B C : ℚ) * (z C : ℚ)
  norm_cast

/-- The rational Gram kernel. -/
def rationalGramKernel (x : V) :
    Submodule ℚ (SecondSubconstituent G x → ℚ) :=
  LinearMap.ker (localGramMatrixRat G x).mulVecLin

theorem rationalGramKernel_finrank
    (hG : IsHypothetical G) (x : V) :
    Module.finrank ℚ (rationalGramKernel G x) = 208 := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (localGramMatrixRat G x).mulVecLin
  rw [Module.finrank_pi] at hnull
  change
    (localGramMatrixRat G x).rank +
        Module.finrank ℚ (rationalGramKernel G x) =
      Fintype.card (SecondSubconstituent G x) at hnull
  rw [localGramMatrixRat_rank G hG x,
    secondSubconstituent_card G hG x] at hnull
  omega

/-- The rational localization of the integral Gram kernel is exactly the
rational Gram kernel. -/
theorem localized_integralGramKernel_eq_rationalGramKernel
    (x : V) :
    (integralGramKernel G x).localized' ℚ ℤ⁰
        (integerToRationalVectors G x) =
      rationalGramKernel G x := by
  rw [integralGramKernel]
  rw [LinearMap.localized'_ker_eq_ker_localizedMap ℚ ℤ⁰
    (integerToRationalVectors G x)
    (integerToRationalVectors G x)]
  change
    LinearMap.ker
        ((localizedIntegralGramMap G x).extendScalarsOfIsLocalization
          ℤ⁰ ℚ) =
      rationalGramKernel G x
  rw [localizedIntegralGramMap_eq_localGramMatrixRat G x]
  rfl

/-- The integral Gram kernel has rank 208. -/
theorem integralGramKernel_finrank
    (hG : IsHypothetical G) (x : V) :
    Module.finrank ℤ (integralGramKernel G x) = 208 := by
  let Kloc :=
    (integralGramKernel G x).localized' ℚ ℤ⁰
      (integerToRationalVectors G x)
  have hlocalization :
      Module.finrank ℤ Kloc =
        Module.finrank ℤ (integralGramKernel G x) := by
    exact
      IsLocalizedModule.finrank_eq ℤ⁰
        ((integralGramKernel G x).toLocalized' ℚ ℤ⁰
          (integerToRationalVectors G x))
        le_rfl
  have hscalars :
      Module.finrank ℚ Kloc = Module.finrank ℤ Kloc := by
    change
      Cardinal.toNat (Module.rank ℚ Kloc) =
        Cardinal.toNat (Module.rank ℤ Kloc)
    exact congrArg Cardinal.toNat
      (IsLocalization.rank_eq (N := Kloc) ℚ ℤ⁰ le_rfl)
  have hrational :
      Module.finrank ℚ Kloc = 208 := by
    rw [show Kloc = rationalGramKernel G x by
      exact localized_integralGramKernel_eq_rationalGramKernel G x]
    exact rationalGramKernel_finrank G hG x
  omega

end SRG266
