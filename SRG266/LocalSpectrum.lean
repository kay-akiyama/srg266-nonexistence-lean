/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.IntersectionBound
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of the local Gram matrix

This file completes the algebraic local-spectrum layer without first
formalizing a general spectral theory of strongly regular graphs.

The integral matrix

`P = 11 L - 6 J`

satisfies `P² = 495 P`.  Hence `R = P / 495` is the support projector of
`L`.  It has trace 12, so its rank is 12.  Two exact factorizations show that
`R` and the real scalar extension of `L` have the same range.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The integral numerator `P = 11 L - 6 J` of the support projector. -/
def localSupportNumerator (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C => 11 * localGramMatrix G x B C - 6

theorem localSupportNumerator_eq_linear_combination
    (x : V) :
    localSupportNumerator G x =
      (11 : ℕ) • localGramMatrix G x -
        (6 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
  ext B C
  change localSupportNumerator G x B C =
    ((11 : ℕ) • localGramMatrix G x) B C -
      ((6 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply]
  simp [localSupportNumerator]

theorem localSupportNumerator_sq
    (hG : IsHypothetical G) (x : V) :
    localSupportNumerator G x * localSupportNumerator G x =
      (495 : ℕ) • localSupportNumerator G x := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let L := localGramMatrix G x
  let P := localSupportNumerator G x
  have hP : P = (11 : ℕ) • L - (6 : ℕ) • J := by
    simpa [P, L, J] using localSupportNumerator_eq_linear_combination G x
  have hLL : L * L = (45 : ℕ) • L + (90 : ℕ) • J := by
    simpa [L, J] using localGramMatrix_sq G hG x
  have hLJ : L * J = (165 : ℕ) • J := by
    simpa [L, J] using localGram_mul_allOnes G hG x
  have hJL : J * L = (165 : ℕ) • J := by
    simpa [L, J] using allOnes_mul_localGram G hG x
  have hJJ : J * J = (220 : ℕ) • J := by
    simpa [J] using allOnesMatrix_sq G hG x
  change P * P = (495 : ℕ) • P
  rw [hP]
  calc
    ((11 : ℕ) • L - (6 : ℕ) • J) *
        ((11 : ℕ) • L - (6 : ℕ) • J) =
      (121 : ℕ) • (L * L) -
        (66 : ℕ) • (L * J + J * L) +
        (36 : ℕ) • (J * J) := by
          noncomm_ring
    _ = (495 : ℕ) • ((11 : ℕ) • L - (6 : ℕ) • J) := by
      rw [hLL, hLJ, hJL, hJJ]
      noncomm_ring

theorem localSupportNumerator_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localSupportNumerator G x * localSupportNumerator G x) B C =
      495 * localSupportNumerator G x B C := by
  have h := congrFun (congrFun (localSupportNumerator_sq G hG x) B) C
  change
    (localSupportNumerator G x * localSupportNumerator G x) B C =
      ((495 : ℕ) • localSupportNumerator G x) B C at h
  rw [nsmulMatrix_apply] at h
  exact h

theorem localSupportNumerator_mul_localGram
    (hG : IsHypothetical G) (x : V) :
    localSupportNumerator G x * localGramMatrix G x =
      (495 : ℕ) • localGramMatrix G x := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let L := localGramMatrix G x
  let P := localSupportNumerator G x
  have hP : P = (11 : ℕ) • L - (6 : ℕ) • J := by
    simpa [P, L, J] using localSupportNumerator_eq_linear_combination G x
  have hLL : L * L = (45 : ℕ) • L + (90 : ℕ) • J := by
    simpa [L, J] using localGramMatrix_sq G hG x
  have hJL : J * L = (165 : ℕ) • J := by
    simpa [L, J] using allOnes_mul_localGram G hG x
  change P * L = (495 : ℕ) • L
  rw [hP]
  noncomm_ring [hLL, hJL]

theorem fifteen_smul_localSupportNumerator
    (hG : IsHypothetical G) (x : V) :
    (15 : ℕ) • localSupportNumerator G x =
      localGramMatrix G x *
        ((210 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) -
          localGramMatrix G x) := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let L := localGramMatrix G x
  let P := localSupportNumerator G x
  have hP : P = (11 : ℕ) • L - (6 : ℕ) • J := by
    simpa [P, L, J] using localSupportNumerator_eq_linear_combination G x
  have hLL : L * L = (45 : ℕ) • L + (90 : ℕ) • J := by
    simpa [L, J] using localGramMatrix_sq G hG x
  change (15 : ℕ) • P = L * ((210 : ℕ) • 1 - L)
  rw [hP]
  noncomm_ring [hLL]

/-- The real scalar extension of the local Gram matrix. -/
def localGramMatrixReal (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℝ :=
  fun B C => localGramMatrix G x B C

/-- The real support projector `R = P / 495`. -/
noncomputable def localSupportProjector (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℝ :=
  fun B C => (localSupportNumerator G x B C : ℝ) / 495

theorem localSupportProjector_idempotent
    (hG : IsHypothetical G) (x : V) :
    localSupportProjector G x * localSupportProjector G x =
      localSupportProjector G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localSupportNumerator G x B D : ℝ) *
            (localSupportNumerator G x D C : ℝ)) =
        ((localSupportNumerator G x * localSupportNumerator G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ D,
      (localSupportNumerator G x B D : ℝ) / 495 *
        ((localSupportNumerator G x D C : ℝ) / 495)) =
      (localSupportNumerator G x B C : ℝ) / 495
  calc
    (∑ D,
        (localSupportNumerator G x B D : ℝ) / 495 *
          ((localSupportNumerator G x D C : ℝ) / 495)) =
        (∑ D,
          (localSupportNumerator G x B D : ℝ) *
            (localSupportNumerator G x D C : ℝ)) / 245025 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localSupportNumerator G x *
          localSupportNumerator G x) B C : ℤ) / 245025 := by
      rw [hcast]
    _ = (localSupportNumerator G x B C : ℝ) / 495 := by
      rw [localSupportNumerator_sq_apply G hG x B C]
      push_cast
      ring

theorem localSupportProjector_trace
    (hG : IsHypothetical G) (x : V) :
    (localSupportProjector G x).trace = 12 := by
  rw [Matrix.trace]
  change
    (∑ B : SecondSubconstituent G x,
      (localSupportNumerator G x B B : ℝ) / 495) = 12
  have hdiag :
      ∀ B : SecondSubconstituent G x,
        localSupportNumerator G x B B = 27 := by
    intro B
    simp [localSupportNumerator, localGramMatrix_diagonal G hG x B]
  simp_rw [hdiag]
  simp [secondSubconstituent_card G hG x]
  norm_num

theorem rank_eq_nat_of_idempotent_trace
    {K : Type*} [Field K] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (n : ℕ)
    (hidempotent : A * A = A)
    (htrace : A.trace = n) :
    A.rank = n := by
  let f : (ι → K) →ₗ[K] (ι → K) := A.toLin'
  have hf : IsIdempotentElem f := by
    change f * f = f
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin' hidempotent
  have hproj : LinearMap.IsProj f.range f :=
    LinearMap.IsIdempotentElem.isProj_range f hf
  have htraceRange := hproj.trace
  rw [Matrix.trace_toLin'_eq, htrace] at htraceRange
  have hfinrank : Module.finrank K f.range = n := by
    exact_mod_cast htraceRange.symm
  rw [Matrix.rank_eq_finrank_range_toLin A
    (Pi.basisFun K ι) (Pi.basisFun K ι), Matrix.toLin_eq_toLin']
  exact hfinrank

theorem localSupportProjector_rank
    (hG : IsHypothetical G) (x : V) :
    (localSupportProjector G x).rank = 12 :=
  rank_eq_nat_of_idempotent_trace
    (localSupportProjector G x) 12
    (localSupportProjector_idempotent G hG x)
    (localSupportProjector_trace G hG x)

theorem localSupportProjector_mul_localGramMatrixReal
    (hG : IsHypothetical G) (x : V) :
    localSupportProjector G x * localGramMatrixReal G x =
      localGramMatrixReal G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localSupportNumerator G x B D : ℝ) *
            (localGramMatrix G x D C : ℝ)) =
        ((localSupportNumerator G x * localGramMatrix G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  have hprod :=
    congrFun (congrFun (localSupportNumerator_mul_localGram G hG x) B) C
  change
    (localSupportNumerator G x * localGramMatrix G x) B C =
      ((495 : ℕ) • localGramMatrix G x) B C at hprod
  rw [nsmulMatrix_apply] at hprod
  change
    (∑ D,
      (localSupportNumerator G x B D : ℝ) / 495 *
        (localGramMatrix G x D C : ℝ)) =
      (localGramMatrix G x B C : ℝ)
  calc
    (∑ D,
        (localSupportNumerator G x B D : ℝ) / 495 *
          (localGramMatrix G x D C : ℝ)) =
        (∑ D,
          (localSupportNumerator G x B D : ℝ) *
            (localGramMatrix G x D C : ℝ)) / 495 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localSupportNumerator G x *
          localGramMatrix G x) B C : ℤ) / 495 := by
      rw [hcast]
    _ = (localGramMatrix G x B C : ℝ) := by
      rw [hprod]
      push_cast
      ring

/-- The integral numerator `210 I - L` of a right factor for the support
projector. -/
def localGramRankFactorNumerator (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C => (if B = C then 210 else 0) - localGramMatrix G x B C

theorem localGramRankFactorNumerator_eq_linear_combination
    (x : V) :
    localGramRankFactorNumerator G x =
      (210 : ℕ) •
          (1 : Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) -
        localGramMatrix G x := by
  ext B C
  change localGramRankFactorNumerator G x B C =
    ((210 : ℕ) •
      (1 : Matrix (SecondSubconstituent G x)
        (SecondSubconstituent G x) ℤ)) B C -
      localGramMatrix G x B C
  rw [nsmulMatrix_apply]
  by_cases hBC : B = C <;>
    simp [localGramRankFactorNumerator, hBC, Matrix.one_apply]

theorem fifteen_smul_localSupportNumerator_factor
    (hG : IsHypothetical G) (x : V) :
    (15 : ℕ) • localSupportNumerator G x =
      localGramMatrix G x * localGramRankFactorNumerator G x := by
  rw [localGramRankFactorNumerator_eq_linear_combination]
  exact fifteen_smul_localSupportNumerator G hG x

/-- A real right factor `T` such that `L T` is the support projector. -/
noncomputable def localGramRankFactor (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℝ :=
  fun B C => (localGramRankFactorNumerator G x B C : ℝ) / 7425

theorem localGramMatrixReal_mul_rankFactor
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixReal G x * localGramRankFactor G x =
      localSupportProjector G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localGramMatrix G x B D : ℝ) *
            (localGramRankFactorNumerator G x D C : ℝ)) =
        ((localGramMatrix G x * localGramRankFactorNumerator G x) B C :
          ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  have hprod :=
    congrFun
      (congrFun (fifteen_smul_localSupportNumerator_factor G hG x) B) C
  change
    ((15 : ℕ) • localSupportNumerator G x) B C =
      (localGramMatrix G x * localGramRankFactorNumerator G x) B C at hprod
  rw [nsmulMatrix_apply] at hprod
  change
    (∑ D,
      (localGramMatrix G x B D : ℝ) *
        ((localGramRankFactorNumerator G x D C : ℝ) / 7425)) =
      (localSupportNumerator G x B C : ℝ) / 495
  calc
    (∑ D,
        (localGramMatrix G x B D : ℝ) *
          ((localGramRankFactorNumerator G x D C : ℝ) / 7425)) =
        (∑ D,
          (localGramMatrix G x B D : ℝ) *
            (localGramRankFactorNumerator G x D C : ℝ)) / 7425 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localGramMatrix G x *
          localGramRankFactorNumerator G x) B C : ℤ) / 7425 := by
      rw [hcast]
    _ = (localSupportNumerator G x B C : ℝ) / 495 := by
      rw [← hprod]
      push_cast
      ring

theorem localGramMatrixReal_rank
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixReal G x).rank = 12 := by
  have hleSupport :
      (localGramMatrixReal G x).rank ≤
        (localSupportProjector G x).rank := by
    calc
      (localGramMatrixReal G x).rank =
          (localSupportProjector G x * localGramMatrixReal G x).rank := by
        rw [localSupportProjector_mul_localGramMatrixReal G hG x]
      _ ≤ (localSupportProjector G x).rank :=
        Matrix.rank_mul_le_left _ _
  have hleGram :
      (localSupportProjector G x).rank ≤
        (localGramMatrixReal G x).rank := by
    calc
      (localSupportProjector G x).rank =
          (localGramMatrixReal G x * localGramRankFactor G x).rank := by
        rw [localGramMatrixReal_mul_rankFactor G hG x]
      _ ≤ (localGramMatrixReal G x).rank :=
        Matrix.rank_mul_le_left _ _
  rw [localSupportProjector_rank G hG x] at hleSupport hleGram
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem realAllOnesMatrix_posSemidef
    (x : V) :
    (allOnesMatrix :
      Matrix (SecondSubconstituent G x)
        (SecondSubconstituent G x) ℝ).PosSemidef := by
  have h :=
    Matrix.posSemidef_vecMulVec_self_star
      (fun _ : SecondSubconstituent G x => (1 : ℝ))
  have heq :
      Matrix.vecMulVec
          (fun _ : SecondSubconstituent G x => (1 : ℝ))
          (star fun _ : SecondSubconstituent G x => (1 : ℝ)) =
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℝ) := by
    ext B C
    simp [Matrix.vecMulVec, allOnesMatrix]
  rw [heq] at h
  exact h

theorem localGramMatrixReal_eq_projectors
    (x : V) :
    localGramMatrixReal G x =
      (45 : ℝ) • localProjectorMatrix G x +
        (3 / 4 : ℝ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℝ) := by
  ext B C
  change
    localGramMatrixReal G x B C =
      ((45 : ℝ) • localProjectorMatrix G x) B C +
        ((3 / 4 : ℝ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℝ)) B C
  rw [Matrix.smul_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  simp only [localGramMatrixReal, localProjectorMatrix,
    allOnesMatrix_apply]
  simp only [localProjectorNumerator]
  push_cast
  ring

theorem localGramMatrixReal_posSemidef
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixReal G x).PosSemidef := by
  rw [localGramMatrixReal_eq_projectors G x]
  exact
    (localProjectorMatrix_posSemidef G hG x).smul (by norm_num)
      |>.add ((realAllOnesMatrix_posSemidef G x).smul (by norm_num))

end SRG266
