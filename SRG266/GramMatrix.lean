/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.LocalGraph

/-!
# The local integral Gram matrix

This file introduces the integral matrix

`L = 9 I + 3 J - S - 3 H`,

where `S = Mᵀ M` and `H` is the adjacency matrix of the second
subconstituent.  The definition is entrywise, which makes the coefficient ring
and the intended scalar actions unambiguous.

The spectral identity and positive-semidefiniteness are deliberately deferred
to later modules.  Here we prove symmetry, diagonal norm three, and the exact
off-diagonal formula.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The local integral Gram matrix `L`. -/
def localGramMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C =>
    (if B = C then 9 else 0) + 3 - localIntersectionMatrix G x B C -
      if (secondSubconstituentGraph G x).Adj B C then 3 else 0

theorem blockIntersection_comm
    (x : V) (B C : SecondSubconstituent G x) :
    blockIntersection G x B C = blockIntersection G x C B := by
  simp [blockIntersection, Finset.inter_comm]

theorem localIntersectionMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localIntersectionMatrix G x B C = localIntersectionMatrix G x C B := by
  rw [localIntersectionMatrix_apply, localIntersectionMatrix_apply,
    blockIntersection_comm G x B C]

theorem localGramMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localGramMatrix G x B C = localGramMatrix G x C B := by
  rw [localGramMatrix, localGramMatrix, localIntersectionMatrix_comm G x B C]
  simp only [eq_comm, SimpleGraph.adj_comm]

theorem localGramMatrix_isSymm (x : V) :
    (localGramMatrix G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => (localGramMatrix_comm G x B C).symm

@[simp]
theorem localGramMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localGramMatrix G x B B = 3 := by
  simp [localGramMatrix, localIntersectionMatrix_diagonal G hG x B]

theorem localGramMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localGramMatrix G x B C = 0 := by
  have hne : B ≠ C := (secondSubconstituentGraph G x).ne_of_adj hBC
  have hGBC : G.Adj (B : V) (C : V) := hBC
  simp [localGramMatrix, hne, hGBC, localIntersectionMatrix_of_adj G hG x hBC]

theorem localGramMatrix_of_not_adj
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C) (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    localGramMatrix G x B C = 3 - (blockIntersection G x B C : ℤ) := by
  have hGBC : ¬G.Adj (B : V) (C : V) := hBC
  simp [localGramMatrix, hne, hGBC, localIntersectionMatrix_apply]

theorem localGramMatrix_off_diagonal
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x} (hne : B ≠ C) :
    localGramMatrix G x B C =
      if (secondSubconstituentGraph G x).Adj B C then 0
      else 3 - (blockIntersection G x B C : ℤ) := by
  by_cases hBC : (secondSubconstituentGraph G x).Adj B C
  · rw [if_pos hBC, localGramMatrix_of_adj G hG x hBC]
  · rw [if_neg hBC, localGramMatrix_of_not_adj G x hne hBC]

theorem localGramMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ C, localGramMatrix G x B C = 165 := by
  have hdiag : (∑ C : SecondSubconstituent G x,
      if B = C then (9 : ℤ) else 0) = 9 := by
    simp
  have hconst : (∑ _C : SecondSubconstituent G x, (3 : ℤ)) = 660 := by
    simp [secondSubconstituent_card G hG x]
  have hS : (∑ C, localIntersectionMatrix G x B C) = 396 := by
    have h := congrFun (localIntersectionMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  have hHrow : (∑ C, localAdjacencyMatrix G x B C) = 36 := by
    have h := congrFun (localAdjacencyMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  have hH : (∑ C : SecondSubconstituent G x,
      if (secondSubconstituentGraph G x).Adj B C then (3 : ℤ) else 0) = 108 := by
    calc
      (∑ C : SecondSubconstituent G x,
          if (secondSubconstituentGraph G x).Adj B C then (3 : ℤ) else 0) =
          3 * ∑ C, localAdjacencyMatrix G x B C := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        by_cases hBC : (secondSubconstituentGraph G x).Adj B C <;>
          simp [localAdjacencyMatrix]
      _ = 108 := by rw [hHrow]; norm_num
  change (∑ C, ((if B = C then (9 : ℤ) else 0) + 3 -
    localIntersectionMatrix G x B C -
    if (secondSubconstituentGraph G x).Adj B C then 3 else 0)) = 165
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hdiag, hconst, hS, hH]
  norm_num

@[simp]
theorem localGramMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localGramMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 165 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localGramMatrix_row_sum G hG x B

/-- The shifted matrix `K = L - J`, defined entrywise. -/
def localKMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C => localGramMatrix G x B C - 1

@[simp]
theorem localKMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localKMatrix G x B B = 2 := by
  simp [localKMatrix, localGramMatrix_diagonal G hG x B]

theorem localKMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localKMatrix G x B C = -1 := by
  rw [localKMatrix, localGramMatrix_of_adj G hG x hBC]
  norm_num

theorem localKMatrix_of_not_adj
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C) (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    localKMatrix G x B C = 2 - (blockIntersection G x B C : ℤ) := by
  rw [localKMatrix, localGramMatrix_of_not_adj G x hne hBC]
  ring

theorem localKMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ C, localKMatrix G x B C = -55 := by
  simp only [localKMatrix]
  rw [Finset.sum_sub_distrib, localGramMatrix_row_sum G hG x B]
  simp [secondSubconstituent_card G hG x]

@[simp]
theorem localKMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localKMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = -55 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localKMatrix_row_sum G hG x B

end SRG266
