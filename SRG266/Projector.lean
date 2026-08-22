/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.LocalAlgebra
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The local rank-eleven projector

This file constructs the primitive projector used for the first local block
intersection bound.  To keep the arithmetic integral for as long as possible,
we first define

`Q = 4 L - 3 J`.

The local matrix identities imply `Q² = 180 Q`.  Dividing by `180` over the
reals gives a symmetric idempotent matrix, hence a positive-semidefinite
matrix.  Its two-by-two principal minors give the first intersection cap.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The integral numerator `Q = 4 L - 3 J` of the local projector. -/
def localProjectorNumerator (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C => 4 * localGramMatrix G x B C - 3

theorem localGram_mul_allOnes
    (hG : IsHypothetical G) (x : V) :
    localGramMatrix G x *
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) =
      (165 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hrow := localGramMatrix_row_sum G hG x B
  simp only [allOnesMatrix_apply, mul_one]
  rw [hrow]
  simp

theorem allOnes_mul_localGram
    (hG : IsHypothetical G) (x : V) :
    (allOnesMatrix :
        Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) *
        localGramMatrix G x =
      (165 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hcol :
      (∑ D, localGramMatrix G x D C) = 165 := by
    calc
      (∑ D, localGramMatrix G x D C) =
          ∑ D, localGramMatrix G x C D := by
        apply Finset.sum_congr rfl
        intro D _
        exact localGramMatrix_comm G x D C
      _ = 165 := localGramMatrix_row_sum G hG x C
  simp only [allOnesMatrix_apply, one_mul]
  rw [hcol]
  simp

theorem localProjectorNumerator_eq_linear_combination
    (x : V) :
    localProjectorNumerator G x =
      (4 : ℕ) • localGramMatrix G x -
        (3 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
  ext B C
  change localProjectorNumerator G x B C =
    ((4 : ℕ) • localGramMatrix G x) B C -
      ((3 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply]
  simp [localProjectorNumerator]

theorem localProjectorNumerator_sq
    (hG : IsHypothetical G) (x : V) :
    localProjectorNumerator G x * localProjectorNumerator G x =
      (180 : ℕ) • localProjectorNumerator G x := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let L := localGramMatrix G x
  let Q := localProjectorNumerator G x
  have hQ : Q = (4 : ℕ) • L - (3 : ℕ) • J := by
    simpa [Q, L, J] using localProjectorNumerator_eq_linear_combination G x
  have hLL : L * L = (45 : ℕ) • L + (90 : ℕ) • J := by
    simpa [L, J] using localGramMatrix_sq G hG x
  have hLJ : L * J = (165 : ℕ) • J := by
    simpa [L, J] using localGram_mul_allOnes G hG x
  have hJL : J * L = (165 : ℕ) • J := by
    simpa [L, J] using allOnes_mul_localGram G hG x
  have hJJ : J * J = (220 : ℕ) • J := by
    simpa [J] using allOnesMatrix_sq G hG x
  change Q * Q = (180 : ℕ) • Q
  rw [hQ]
  calc
    ((4 : ℕ) • L - (3 : ℕ) • J) *
        ((4 : ℕ) • L - (3 : ℕ) • J) =
      (16 : ℕ) • (L * L) -
        (12 : ℕ) • (L * J + J * L) +
        (9 : ℕ) • (J * J) := by
          noncomm_ring
    _ = (180 : ℕ) • ((4 : ℕ) • L - (3 : ℕ) • J) := by
      rw [hLL, hLJ, hJL, hJJ]
      noncomm_ring

theorem localProjectorNumerator_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localProjectorNumerator G x * localProjectorNumerator G x) B C =
      180 * localProjectorNumerator G x B C := by
  have h :=
    congrFun (congrFun (localProjectorNumerator_sq G hG x) B) C
  change
    (localProjectorNumerator G x * localProjectorNumerator G x) B C =
      ((180 : ℕ) • localProjectorNumerator G x) B C at h
  rw [nsmulMatrix_apply] at h
  exact h

/-- The real primitive projector `E = Q / 180`. -/
noncomputable def localProjectorMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℝ :=
  fun B C => (localProjectorNumerator G x B C : ℝ) / 180

theorem localProjectorMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localProjectorMatrix G x B C = localProjectorMatrix G x C B := by
  simp only [localProjectorMatrix, localProjectorNumerator]
  rw [localGramMatrix_comm G x B C]

theorem localProjectorMatrix_isHermitian (x : V) :
    (localProjectorMatrix G x).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact Matrix.IsSymm.ext fun B C =>
    (localProjectorMatrix_comm G x B C).symm

theorem localProjectorMatrix_idempotent
    (hG : IsHypothetical G) (x : V) :
    localProjectorMatrix G x * localProjectorMatrix G x =
      localProjectorMatrix G x := by
  ext B C
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localProjectorNumerator G x B D : ℝ) *
            (localProjectorNumerator G x D C : ℝ)) =
        ((localProjectorNumerator G x * localProjectorNumerator G x) B C :
          ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ D,
      (localProjectorNumerator G x B D : ℝ) / 180 *
        ((localProjectorNumerator G x D C : ℝ) / 180)) =
      (localProjectorNumerator G x B C : ℝ) / 180
  calc
    (∑ D,
        (localProjectorNumerator G x B D : ℝ) / 180 *
          ((localProjectorNumerator G x D C : ℝ) / 180)) =
        (∑ D,
          (localProjectorNumerator G x B D : ℝ) *
            (localProjectorNumerator G x D C : ℝ)) / 32400 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ((localProjectorNumerator G x *
          localProjectorNumerator G x) B C : ℤ) / 32400 := by
      rw [hcast]
    _ = (localProjectorNumerator G x B C : ℝ) / 180 := by
      rw [localProjectorNumerator_sq_apply G hG x B C]
      push_cast
      ring

theorem localProjectorMatrix_posSemidef
    (hG : IsHypothetical G) (x : V) :
    (localProjectorMatrix G x).PosSemidef := by
  have h :=
    Matrix.posSemidef_conjTranspose_mul_self (localProjectorMatrix G x)
  rw [(localProjectorMatrix_isHermitian G x).eq,
    localProjectorMatrix_idempotent G hG x] at h
  exact h

@[simp]
theorem localProjectorMatrix_diagonal
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    localProjectorMatrix G x B B = 1 / 20 := by
  simp [localProjectorMatrix, localProjectorNumerator,
    localGramMatrix_diagonal G hG x B]
  norm_num

theorem localProjectorMatrix_of_not_adj
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    localProjectorMatrix G x B C =
      (9 - 4 * (blockIntersection G x B C : ℝ)) / 180 := by
  rw [localProjectorMatrix, localProjectorNumerator,
    localGramMatrix_of_not_adj G x hne hBC]
  push_cast
  ring

theorem localProjectorMatrix_entry_sq_le
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    localProjectorMatrix G x B C ^ 2 ≤
      localProjectorMatrix G x B B * localProjectorMatrix G x C C := by
  let e : Fin 2 → SecondSubconstituent G x :=
    fun i => if i = 0 then B else C
  have hminor :
      ((localProjectorMatrix G x).submatrix e e).PosSemidef :=
    (localProjectorMatrix_posSemidef G hG x).submatrix e
  have hdet :
      0 ≤ ((localProjectorMatrix G x).submatrix e e).det :=
    hminor.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply] at hdet
  have he0 : e 0 = B := by simp [e]
  have he1 : e 1 = C := by simp [e]
  rw [he0, he1, localProjectorMatrix_comm G x C B] at hdet
  nlinarith

theorem blockIntersection_le_four_of_not_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    blockIntersection G x B C ≤ 4 := by
  have hsq := localProjectorMatrix_entry_sq_le G hG x B C
  rw [localProjectorMatrix_diagonal G hG x B,
    localProjectorMatrix_diagonal G hG x C,
    localProjectorMatrix_of_not_adj G x hne hBC] at hsq
  by_contra hcap
  have hi : 5 ≤ blockIntersection G x B C := by omega
  have hiReal : (5 : ℝ) ≤ blockIntersection G x B C := by
    exact_mod_cast hi
  have hnonneg : (0 : ℝ) ≤ blockIntersection G x B C := by positivity
  have hprod :
      0 ≤ (2 * (blockIntersection G x B C : ℝ) + 1) *
        ((blockIntersection G x B C : ℝ) - 5) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  norm_num at hsq
  nlinarith

theorem blockIntersection_le_four
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C) :
    blockIntersection G x B C ≤ 4 := by
  by_cases hBC : (secondSubconstituentGraph G x).Adj B C
  · rw [blockIntersection_of_adj G hG x hBC]
    norm_num
  · exact blockIntersection_le_four_of_not_adj G hG x hne hBC

end SRG266
