/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.GramMatrix
import Mathlib.Tactic.NoncommRing

/-!
# The local matrix algebra

This file develops the product identities among the local incidence matrix
`M`, block-intersection matrix `S`, and second-subconstituent adjacency matrix
`H`.  All identities are proved from finite common-neighbor counts.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Second-subconstituent vertices which are both incident with `p` and
adjacent to `C`. -/
def incidenceNeighborOccurrences
    (x : V) (p : FirstSubconstituent G x) (C : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) :=
  Finset.univ.filter fun D =>
    p ∈ localBlock G x D ∧ (secondSubconstituentGraph G x).Adj D C

/-- Common neighbors of a first-subconstituent point and a
second-subconstituent vertex are exactly the occurrences counted by `M H`. -/
def firstSecondCommonNeighborsEquiv
    (hG : IsHypothetical G) (x : V)
    (p : FirstSubconstituent G x) (C : SecondSubconstituent G x) :
    G.commonNeighbors (p : V) (C : V) ≃
      ↥(incidenceNeighborOccurrences G x p C) where
  toFun z := by
    have hnotxz : ¬G.Adj x (z : V) :=
      not_adj_root_of_adj_first G hG x p z.property.1
    have hxne : x ≠ (z : V) := by
      intro hxz
      have hxC : ¬G.Adj x (C : V) := ((G.compl_adj x C).mp C.property).2
      apply hxC
      simpa [hxz] using z.property.2.symm
    let D : SecondSubconstituent G x :=
      ⟨z, (G.compl_adj x z).mpr ⟨hxne, hnotxz⟩⟩
    refine ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨(mem_localBlock G x D p).mpr z.property.1,
      z.property.2.symm⟩
  invFun D := by
    have hD := Finset.mem_filter.mp D.property
    exact ⟨D.1, ⟨(mem_localBlock G x D.1 p).mp hD.2.1,
      hD.2.2.symm⟩⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv D := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem localIncidence_mul_adjacency_apply_card
    (hG : IsHypothetical G) (x : V)
    (p : FirstSubconstituent G x) (C : SecondSubconstituent G x) :
    (localIncidenceMatrix G x * localAdjacencyMatrix G x) p C =
      Fintype.card (G.commonNeighbors (p : V) (C : V)) := by
  rw [Matrix.mul_apply]
  calc
    (∑ D, localIncidenceMatrix G x p D * localAdjacencyMatrix G x D C) =
        ((incidenceNeighborOccurrences G x p C).card : ℤ) := by
      simp only [localIncidenceMatrix, localAdjacencyMatrix,
        SimpleGraph.adjMatrix_apply, ite_zero_mul_ite_zero, one_mul,
        Finset.sum_boole]
      norm_cast
    _ = Fintype.card (G.commonNeighbors (p : V) (C : V)) := by
      norm_cast
      rw [← Fintype.card_coe]
      exact (Fintype.card_congr (firstSecondCommonNeighborsEquiv G hG x p C)).symm

theorem localIncidence_mul_adjacency_apply
    (hG : IsHypothetical G) (x : V)
    (p : FirstSubconstituent G x) (C : SecondSubconstituent G x) :
    (localIncidenceMatrix G x * localAdjacencyMatrix G x) p C =
      if p ∈ localBlock G x C then 0 else 9 := by
  rw [localIncidence_mul_adjacency_apply_card G hG x p C]
  have hne : (p : V) ≠ (C : V) := by
    intro hpC
    have hnot : ¬G.Adj x (C : V) := ((G.compl_adj x C).mp C.property).2
    exact hnot (hpC ▸ p.property)
  by_cases hpC : p ∈ localBlock G x C
  · rw [if_pos hpC, hG.of_adj p C ((mem_localBlock G x C p).mp hpC)]
    norm_num
  · have hnot : ¬G.Adj (p : V) (C : V) :=
      fun h => hpC ((mem_localBlock G x C p).mpr h)
    rw [if_neg hpC, hG.of_not_adj hne hnot]
    norm_num

theorem localIncidence_mul_adjacency
    (hG : IsHypothetical G) (x : V) :
    localIncidenceMatrix G x * localAdjacencyMatrix G x =
      fun p C => if p ∈ localBlock G x C then 0 else 9 := by
  ext p C
  exact localIncidence_mul_adjacency_apply G hG x p C

theorem localIntersection_mul_adjacency_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localIntersectionMatrix G x * localAdjacencyMatrix G x) B C =
      81 - 9 * localIntersectionMatrix G x B C := by
  have hS :
      (∑ p, localIncidenceMatrix G x p B * localIncidenceMatrix G x p C) =
        localIntersectionMatrix G x B C := by
    symm
    rw [localIntersectionMatrix, Matrix.mul_apply]
    rfl
  calc
    (localIntersectionMatrix G x * localAdjacencyMatrix G x) B C =
        ∑ p, localIncidenceMatrix G x p B *
          (localIncidenceMatrix G x * localAdjacencyMatrix G x) p C := by
      rw [localIntersectionMatrix, Matrix.mul_assoc, Matrix.mul_apply]
      rfl
    _ = ∑ p, localIncidenceMatrix G x p B *
        (if p ∈ localBlock G x C then 0 else 9) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [localIncidence_mul_adjacency_apply G hG x p C]
    _ = ∑ p, (9 * localIncidenceMatrix G x p B -
        9 * (localIncidenceMatrix G x p B * localIncidenceMatrix G x p C)) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hpB : p ∈ localBlock G x B <;>
        by_cases hpC : p ∈ localBlock G x C <;>
          simp [localIncidenceMatrix, hpB, hpC]
    _ = 9 * (∑ p, localIncidenceMatrix G x p B) -
        9 * (∑ p, localIncidenceMatrix G x p B *
          localIncidenceMatrix G x p C) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 81 - 9 * localIntersectionMatrix G x B C := by
      rw [localIncidenceMatrix_column_sum G hG x B, hS]
      norm_num

theorem localAdjacency_mul_intersection_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localAdjacencyMatrix G x * localIntersectionMatrix G x) B C =
      81 - 9 * localIntersectionMatrix G x B C := by
  calc
    (localAdjacencyMatrix G x * localIntersectionMatrix G x) B C =
        (localIntersectionMatrix G x * localAdjacencyMatrix G x) C B := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro D _
      rw [localIntersectionMatrix_comm G x D C]
      simp [localAdjacencyMatrix, SimpleGraph.adj_comm, mul_comm]
    _ = 81 - 9 * localIntersectionMatrix G x C B :=
      localIntersection_mul_adjacency_apply G hG x C B
    _ = 81 - 9 * localIntersectionMatrix G x B C := by
      rw [localIntersectionMatrix_comm G x C B]

theorem localIntersection_mul_adjacency
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x * localAdjacencyMatrix G x =
      fun B C => 81 - 9 * localIntersectionMatrix G x B C := by
  ext B C
  exact localIntersection_mul_adjacency_apply G hG x B C

theorem localAdjacency_mul_intersection
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x * localIntersectionMatrix G x =
      fun B C => 81 - 9 * localIntersectionMatrix G x B C := by
  ext B C
  exact localAdjacency_mul_intersection_apply G hG x B C

theorem pointGram_mul_incidence_apply
    (hG : IsHypothetical G) (x : V)
    (p : FirstSubconstituent G x) (C : SecondSubconstituent G x) :
    ((localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) *
        localIncidenceMatrix G x) p C =
      36 * localIncidenceMatrix G x p C + 72 := by
  rw [Matrix.mul_apply]
  calc
    (∑ q, (localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) p q *
        localIncidenceMatrix G x q C) =
        ∑ q, (8 * localIncidenceMatrix G x q C +
          if p = q then 36 * localIncidenceMatrix G x q C else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [localIncidence_mul_transpose_apply G hG x p q]
      by_cases hpq : p = q
      · simp [hpq]
        ring
      · simp [hpq]
    _ = 8 * (∑ q, localIncidenceMatrix G x q C) +
        36 * localIncidenceMatrix G x p C := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ = 36 * localIncidenceMatrix G x p C + 72 := by
      rw [localIncidenceMatrix_column_sum G hG x C]
      ring

theorem localIntersectionMatrix_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localIntersectionMatrix G x * localIntersectionMatrix G x) B C =
      36 * localIntersectionMatrix G x B C + 648 := by
  have hassoc :
      localIntersectionMatrix G x * localIntersectionMatrix G x =
        (localIncidenceMatrix G x)ᵀ *
          (((localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) *
            localIncidenceMatrix G x)) := by
    simp only [localIntersectionMatrix, Matrix.mul_assoc]
  rw [hassoc, Matrix.mul_apply]
  have hS :
      (∑ p, localIncidenceMatrix G x p B * localIncidenceMatrix G x p C) =
        localIntersectionMatrix G x B C := by
    symm
    rw [localIntersectionMatrix, Matrix.mul_apply]
    rfl
  calc
    (∑ p, (localIncidenceMatrix G x)ᵀ B p *
        ((localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) *
          localIncidenceMatrix G x) p C) =
        ∑ p, localIncidenceMatrix G x p B *
          (36 * localIncidenceMatrix G x p C + 72) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.transpose_apply, pointGram_mul_incidence_apply G hG x p C]
    _ = 36 * (∑ p, localIncidenceMatrix G x p B *
        localIncidenceMatrix G x p C) +
        72 * (∑ p, localIncidenceMatrix G x p B) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 36 * localIntersectionMatrix G x B C + 648 := by
      rw [hS, localIncidenceMatrix_column_sum G hG x B]
      norm_num

theorem localIntersectionMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x * localIntersectionMatrix G x =
      fun B C => 36 * localIntersectionMatrix G x B C + 648 := by
  ext B C
  exact localIntersectionMatrix_sq_apply G hG x B C

@[simp]
theorem natCastMatrix_mul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : Matrix ι ι ℤ) (i j : ι) :
    ((n : Matrix ι ι ℤ) * A) i j = n * A i j := by
  rw [Matrix.mul_apply]
  simp [Matrix.natCast_apply]

theorem nsmulMatrix_apply
    {m n : Type*} (k : ℕ) (A : Matrix m n ℤ) (i : m) (j : n) :
    (k • A) i j = (k : ℤ) * A i j := by
  rw [Matrix.smul_apply, nsmul_eq_mul]

theorem allOnesMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    (allOnesMatrix :
        Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) *
        allOnesMatrix =
      (220 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  simp [secondSubconstituent_card G hG x]

theorem allOnes_mul_intersection
    (hG : IsHypothetical G) (x : V) :
    (allOnesMatrix :
        Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) *
        localIntersectionMatrix G x =
      (396 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hcol :
      (∑ D, localIntersectionMatrix G x D C) = 396 := by
    calc
      (∑ D, localIntersectionMatrix G x D C) =
          ∑ D, localIntersectionMatrix G x C D := by
        apply Finset.sum_congr rfl
        intro D _
        exact localIntersectionMatrix_comm G x D C
      _ = 396 := by
        have h := congrFun (localIntersectionMatrix_mulVec_one G hG x) C
        simpa [Matrix.mulVec_apply_eq_sum] using h
  simp only [allOnesMatrix_apply, one_mul]
  rw [hcol]
  simp

theorem intersection_mul_allOnes
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x *
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) =
      (396 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hrow :
      (∑ D, localIntersectionMatrix G x B D) = 396 := by
    have h := congrFun (localIntersectionMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  simp only [allOnesMatrix_apply, mul_one]
  rw [hrow]
  simp

theorem allOnes_mul_adjacency
    (hG : IsHypothetical G) (x : V) :
    (allOnesMatrix :
        Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) *
        localAdjacencyMatrix G x =
      (36 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hcol :
      (∑ D, localAdjacencyMatrix G x D C) = 36 := by
    calc
      (∑ D, localAdjacencyMatrix G x D C) =
          ∑ D, localAdjacencyMatrix G x C D := by
        apply Finset.sum_congr rfl
        intro D _
        simp [localAdjacencyMatrix, SimpleGraph.adj_comm]
      _ = 36 := by
        have h := congrFun (localAdjacencyMatrix_mulVec_one G hG x) C
        simpa [Matrix.mulVec_apply_eq_sum] using h
  simp only [allOnesMatrix_apply, one_mul]
  rw [hcol]
  simp

theorem adjacency_mul_allOnes
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x *
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) =
      (36 : ℕ) • allOnesMatrix := by
  ext B C
  rw [Matrix.mul_apply]
  have hrow :
      (∑ D, localAdjacencyMatrix G x B D) = 36 := by
    have h := congrFun (localAdjacencyMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  simp only [allOnesMatrix_apply, mul_one]
  rw [hrow]
  simp

theorem localGramMatrix_eq_linear_combination
    (x : V) :
    localGramMatrix G x =
      (9 : ℕ) •
          (1 : Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) +
        (3 : ℕ) • allOnesMatrix -
        localIntersectionMatrix G x -
        (3 : ℕ) • localAdjacencyMatrix G x := by
  ext B C
  change localGramMatrix G x B C =
    ((9 : ℕ) •
        (1 : Matrix (SecondSubconstituent G x)
          (SecondSubconstituent G x) ℤ)) B C +
      ((3 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C -
      localIntersectionMatrix G x B C -
      ((3 : ℕ) • localAdjacencyMatrix G x) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply, nsmulMatrix_apply]
  by_cases hBC : B = C <;>
    simp [localGramMatrix, localAdjacencyMatrix, hBC, Matrix.one_apply]

theorem localIntersectionMatrix_sq_linear_combination
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x * localIntersectionMatrix G x =
      (36 : ℕ) • localIntersectionMatrix G x +
        (648 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
  ext B C
  rw [localIntersectionMatrix_sq_apply G hG x B C]
  change 36 * localIntersectionMatrix G x B C + 648 =
    ((36 : ℕ) • localIntersectionMatrix G x) B C +
      ((648 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply]
  simp

theorem localIntersection_mul_adjacency_linear_combination
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x * localAdjacencyMatrix G x =
      (81 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) -
        (9 : ℕ) • localIntersectionMatrix G x := by
  ext B C
  rw [localIntersection_mul_adjacency_apply G hG x B C]
  change 81 - 9 * localIntersectionMatrix G x B C =
    ((81 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C -
      ((9 : ℕ) • localIntersectionMatrix G x) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply]
  simp

theorem localAdjacency_mul_intersection_linear_combination
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x * localIntersectionMatrix G x =
      (81 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) -
        (9 : ℕ) • localIntersectionMatrix G x := by
  ext B C
  rw [localAdjacency_mul_intersection_apply G hG x B C]
  change 81 - 9 * localIntersectionMatrix G x B C =
    ((81 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C -
      ((9 : ℕ) • localIntersectionMatrix G x) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply]
  simp

theorem localAdjacencyMatrix_sq_linear_combination
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x * localAdjacencyMatrix G x =
      (36 : ℕ) •
          (1 : Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) +
        (9 : ℕ) • allOnesMatrix -
        localIntersectionMatrix G x -
        (9 : ℕ) • localAdjacencyMatrix G x := by
  ext B C
  rw [localAdjacencyMatrix_sq G hG x]
  change
    (if B = C then (36 : ℤ) else 0) + 9 -
        localIntersectionMatrix G x B C -
        (if (secondSubconstituentGraph G x).Adj B C then 9 else 0) =
      ((36 : ℕ) •
          (1 : Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ)) B C +
        ((9 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ)) B C -
        localIntersectionMatrix G x B C -
        ((9 : ℕ) • localAdjacencyMatrix G x) B C
  rw [nsmulMatrix_apply, nsmulMatrix_apply, nsmulMatrix_apply]
  by_cases hBC : B = C <;>
    simp [localAdjacencyMatrix, hBC, Matrix.one_apply]

theorem localGramMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    localGramMatrix G x * localGramMatrix G x =
      (45 : ℕ) • localGramMatrix G x +
        (90 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let S := localIntersectionMatrix G x
  let H := localAdjacencyMatrix G x
  have hL :
      localGramMatrix G x =
        (9 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) +
          (3 : ℕ) • J - S - (3 : ℕ) • H := by
    simpa [J, S, H] using localGramMatrix_eq_linear_combination G x
  have hJJ : J * J = (220 : ℕ) • J := by
    simpa [J] using allOnesMatrix_sq G hG x
  have hJS : J * S = (396 : ℕ) • J := by
    simpa [J, S] using allOnes_mul_intersection G hG x
  have hSJ : S * J = (396 : ℕ) • J := by
    simpa [J, S] using intersection_mul_allOnes G hG x
  have hJH : J * H = (36 : ℕ) • J := by
    simpa [J, H] using allOnes_mul_adjacency G hG x
  have hHJ : H * J = (36 : ℕ) • J := by
    simpa [J, H] using adjacency_mul_allOnes G hG x
  have hSS : S * S = (36 : ℕ) • S + (648 : ℕ) • J := by
    simpa [J, S] using localIntersectionMatrix_sq_linear_combination G hG x
  have hSH : S * H = (81 : ℕ) • J - (9 : ℕ) • S := by
    simpa [J, S, H] using
      localIntersection_mul_adjacency_linear_combination G hG x
  have hHS : H * S = (81 : ℕ) • J - (9 : ℕ) • S := by
    simpa [J, S, H] using
      localAdjacency_mul_intersection_linear_combination G hG x
  have hHH :
      H * H =
        (36 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) +
          (9 : ℕ) • J - S - (9 : ℕ) • H := by
    simpa [J, S, H] using
      localAdjacencyMatrix_sq_linear_combination G hG x
  calc
    localGramMatrix G x * localGramMatrix G x =
        (81 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) +
          (54 : ℕ) • J -
          (18 : ℕ) • S -
          (54 : ℕ) • H +
          (9 : ℕ) • (J * J) -
          (3 : ℕ) • (J * S + S * J) -
          (9 : ℕ) • (J * H + H * J) +
          S * S +
          (3 : ℕ) • (S * H + H * S) +
          (9 : ℕ) • (H * H) := by
      rw [hL]
      noncomm_ring
    _ = (45 : ℕ) • localGramMatrix G x + (90 : ℕ) • J := by
      rw [hJJ, hJS, hSJ, hJH, hHJ, hSS, hSH, hHS, hHH, hL]
      noncomm_ring
    _ = (45 : ℕ) • localGramMatrix G x +
        (90 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
      rfl

theorem localGramMatrix_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localGramMatrix G x * localGramMatrix G x) B C =
      45 * localGramMatrix G x B C + 90 := by
  have h := congrFun (congrFun (localGramMatrix_sq G hG x) B) C
  change
    (localGramMatrix G x * localGramMatrix G x) B C =
      ((45 : ℕ) • localGramMatrix G x) B C +
        ((90 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ)) B C at h
  rw [nsmulMatrix_apply, nsmulMatrix_apply] at h
  simpa using h

/-- The local Gram form kills the nonconstant part of the block-intersection
matrix.  Equivalently, the image of `S` seen from the rank-twelve Gram space
is only its all-ones component.

This small identity is useful for integral profile arguments: multiplying an
affine `L`-eigenvector equation by `S` exposes divisibility information which
is invisible from `L` alone. -/
theorem localGram_mul_intersection
    (hG : IsHypothetical G) (x : V) :
    localGramMatrix G x * localIntersectionMatrix G x =
      (297 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let S := localIntersectionMatrix G x
  let H := localAdjacencyMatrix G x
  have hL :
      localGramMatrix G x =
        (9 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) +
          (3 : ℕ) • J - S - (3 : ℕ) • H := by
    simpa [J, S, H] using localGramMatrix_eq_linear_combination G x
  have hJS : J * S = (396 : ℕ) • J := by
    simpa [J, S] using allOnes_mul_intersection G hG x
  have hSS : S * S = (36 : ℕ) • S + (648 : ℕ) • J := by
    simpa [J, S] using localIntersectionMatrix_sq_linear_combination G hG x
  have hHS : H * S = (81 : ℕ) • J - (9 : ℕ) • S := by
    simpa [J, S, H] using
      localAdjacency_mul_intersection_linear_combination G hG x
  calc
    localGramMatrix G x * localIntersectionMatrix G x =
        ((9 : ℕ) •
            (1 : Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) +
          (3 : ℕ) • J - S - (3 : ℕ) • H) * S := by
      rw [hL]
    _ = (9 : ℕ) • S + (3 : ℕ) • (J * S) - S * S -
        (3 : ℕ) • (H * S) := by
      noncomm_ring
    _ = (297 : ℕ) • J := by
      rw [hJS, hSS, hHS]
      noncomm_ring
    _ = (297 : ℕ) •
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) := by
      rfl

end SRG266
