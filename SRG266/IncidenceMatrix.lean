/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.LocalDesign

/-!
# The local incidence matrix

This file defines the integral `45 × 220` incidence matrix `M` of the local
design.  It proves the standard point-Gram identity

`M Mᵀ = 36 I + 8 J`

and identifies each entry of `Mᵀ M` with a block-intersection cardinality.
-/

open scoped BigOperators Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The integral incidence matrix of the local block occurrences. -/
def localIncidenceMatrix (x : V) :
    Matrix (FirstSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun p B => if p ∈ localBlock G x B then 1 else 0

/-- The all-ones matrix. -/
def allOnesMatrix {m n R : Type*} [One R] : Matrix m n R :=
  fun _ _ => 1

@[simp]
theorem allOnesMatrix_apply {m n R : Type*} [One R] (i : m) (j : n) :
    (allOnesMatrix : Matrix m n R) i j = 1 :=
  rfl

theorem localIncidenceMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (p : FirstSubconstituent G x) :
    ∑ B, localIncidenceMatrix G x p B = 44 := by
  calc
    ∑ B, localIncidenceMatrix G x p B =
        ((blocksThrough G x p).card : ℤ) := by
      simp [localIncidenceMatrix, blocksThrough]
    _ = 44 := by
      rw [blocksThrough_card G hG x p]
      norm_num

theorem localIncidenceMatrix_column_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ p, localIncidenceMatrix G x p B = 9 := by
  calc
    ∑ p, localIncidenceMatrix G x p B = ((localBlock G x B).card : ℤ) := by
      simp only [localIncidenceMatrix, Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext p
      simp
    _ = 9 := by
      rw [localBlock_card G hG x B]
      norm_num

@[simp]
theorem localIncidenceMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localIncidenceMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 44 := by
  funext p
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localIncidenceMatrix_row_sum G hG x p

@[simp]
theorem localIncidenceMatrix_transpose_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    (localIncidenceMatrix G x)ᵀ *ᵥ (1 : FirstSubconstituent G x → ℤ) = 9 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, Pi.one_apply, mul_one]
  exact localIncidenceMatrix_column_sum G hG x B

/-- The point Gram matrix has diagonal 44 and off-diagonal entries 8. -/
theorem localIncidence_mul_transpose_apply
    (hG : IsHypothetical G) (x : V)
    (p q : FirstSubconstituent G x) :
    (localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) p q =
      if p = q then 44 else 8 := by
  rw [Matrix.mul_apply]
  by_cases hpq : p = q
  · subst q
    simp only [Matrix.transpose_apply, if_pos]
    calc
      ∑ B, localIncidenceMatrix G x p B * localIncidenceMatrix G x p B =
          ∑ B, localIncidenceMatrix G x p B := by
        apply Finset.sum_congr rfl
        intro B _
        simp [localIncidenceMatrix]
      _ = 44 := localIncidenceMatrix_row_sum G hG x p
  · simp only [Matrix.transpose_apply, if_neg hpq]
    calc
      ∑ B, localIncidenceMatrix G x p B * localIncidenceMatrix G x q B =
          ((blocksThroughPair G x p q).card : ℤ) := by
        simp only [localIncidenceMatrix, ite_zero_mul_ite_zero, one_mul,
          Finset.sum_boole]
        norm_cast
      _ = 8 := by
        rw [blocksThroughPair_card G hG x hpq]
        norm_num

/-- The standard point-Gram identity of the local `2`-design. -/
theorem localIncidence_mul_transpose
    (hG : IsHypothetical G) (x : V) :
    localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ =
      (36 : ℤ) •
          (1 : Matrix (FirstSubconstituent G x) (FirstSubconstituent G x) ℤ) +
        (8 : ℤ) • allOnesMatrix := by
  ext p q
  rw [localIncidence_mul_transpose_apply G hG x p q]
  by_cases hpq : p = q
  · subst q
    simp [Algebra.smul_def, Matrix.mul_apply, Matrix.ofNat_apply]
  · simp [Algebra.smul_def, Matrix.mul_apply, Matrix.ofNat_apply, hpq]

/-- The number of points in the intersection of two local blocks. -/
def blockIntersection (x : V) (B C : SecondSubconstituent G x) : ℕ :=
  (localBlock G x B ∩ localBlock G x C).card

/-- The block-intersection matrix `S = Mᵀ M`. -/
def localIntersectionMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  (localIncidenceMatrix G x)ᵀ * localIncidenceMatrix G x

@[simp]
theorem localIntersectionMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 396 := by
  rw [localIntersectionMatrix, ← Matrix.mulVec_mulVec,
    localIncidenceMatrix_mulVec_one G hG x]
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  change (∑ p, localIncidenceMatrix G x p B * 44) = 396
  calc
    (∑ p, localIncidenceMatrix G x p B * 44) =
        (∑ p, localIncidenceMatrix G x p B) * 44 := by rw [Finset.sum_mul]
    _ = 9 * 44 := by rw [localIncidenceMatrix_column_sum G hG x B]
    _ = 396 := by norm_num

theorem localIntersectionMatrix_apply
    (x : V) (B C : SecondSubconstituent G x) :
    localIntersectionMatrix G x B C = blockIntersection G x B C := by
  rw [localIntersectionMatrix, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, localIncidenceMatrix, ite_zero_mul_ite_zero, one_mul,
    Finset.sum_boole]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp

@[simp]
theorem blockIntersection_self
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    blockIntersection G x B B = 9 := by
  simp [blockIntersection, localBlock_card G hG x B]

@[simp]
theorem localIntersectionMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localIntersectionMatrix G x B B = 9 := by
  rw [localIntersectionMatrix_apply, blockIntersection_self G hG x B]
  norm_num

end SRG266
