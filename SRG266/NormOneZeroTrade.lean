/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.NormOneCoclique
import Mathlib.Algebra.Order.Chebyshev

/-!
# Zero-centroid norm-one profiles are trivial

A zero-centroid ternary profile is a signed trade in the local
`2-(45,9,8)` design and a `-12` eigenvector of the second-subconstituent
adjacency matrix.  These two facts are incompatible with the projector bound.

If `q` is the number of positive (and hence negative) entries and `T` is the
total intersection size between positive and negative blocks, then

* the projector bound gives `q ≤ 22`;
* equality of the signed point degrees and Cauchy--Schwarz give
  `9 q² ≤ 5 T`;
* the `-12` adjacency equation gives at least `12 q` adjacent positive-negative
  pairs;
* adjacent local blocks are disjoint and every other distinct pair intersects
  in at most three points, so `T ≤ 3 q (q - 12)`.

Consequently `q = 0` or `q ≥ 30`; the projector bound leaves only `q = 0`.
No host classification or finite shell search enters the argument.
-/

open scoped Matrix

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Rank15EmbeddingWitness

/-- A norm-one direction with zero centroid coordinate is orthogonal to every
distinguished local Gram generator. -/
theorem directionProfile_eq_zero_of_centroid_eq_zero
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (ht : E.centroidCoordinate (G := G) c u = 0)
    (B₀ : SecondSubconstituent G x) :
    E.directionProfile (G := G) u B₀ = 0 := by
  let a : SecondSubconstituent G x → ℤ :=
    E.directionProfile (G := G) u
  let p : SecondSubconstituent G x → ℤ :=
    fun B => if a B = 1 then 1 else 0
  let n : SecondSubconstituent G x → ℤ :=
    fun B => if a B = -1 then 1 else 0
  have hacases (B : SecondSubconstituent G x) :
      a B = -1 ∨ a B = 0 ∨ a B = 1 := by
    exact E.directionProfile_cases (G := G) hG u hu B
  have ha_eq (B : SecondSubconstituent G x) : a B = p B - n B := by
    rcases hacases B with hneg | hzero | hone
    · simp [p, n, hneg]
    · simp [p, n, hzero]
    · simp [p, n, hone]
  have ha_sq (B : SecondSubconstituent G x) : a B ^ 2 = p B + n B := by
    rcases hacases B with hneg | hzero | hone
    · simp [p, n, hneg]
    · simp [p, n, hzero]
    · simp [p, n, hone]
  have hp_nonneg (B : SecondSubconstituent G x) : 0 ≤ p B := by
    by_cases hB : a B = 1 <;> simp [p, hB]
  have hn_nonneg (B : SecondSubconstituent G x) : 0 ≤ n B := by
    by_cases hB : a B = -1 <;> simp [n, hB]
  have hsum_a : ∑ B, a B = 0 := by
    simpa [a, ht] using E.directionProfile_sum (G := G) c hc u
  have hsum_pn : ∑ B, p B = ∑ B, n B := by
    have hdiff : (∑ B, p B) - ∑ B, n B = 0 := by
      calc
        (∑ B, p B) - ∑ B, n B = ∑ B, (p B - n B) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ B, a B := by
          apply Finset.sum_congr rfl
          intro B _
          rw [ha_eq]
        _ = 0 := hsum_a
    omega
  let q : ℤ := ∑ B, p B
  have hq_nonneg : 0 ≤ q := by
    exact Finset.sum_nonneg fun B _ => hp_nonneg B
  have hsquare : ∑ B, a B ^ 2 = 2 * q := by
    calc
      ∑ B, a B ^ 2 = ∑ B, (p B + n B) := by
        apply Finset.sum_congr rfl
        intro B _
        rw [ha_sq]
      _ = (∑ B, p B) + ∑ B, n B := Finset.sum_add_distrib
      _ = 2 * q := by
        simp only [q]
        rw [hsum_pn]
        ring
  have hq_le : q ≤ 22 := by
    have hupper := E.directionProfile_upper_bound (G := G) hG c hc u hu
    simp [directionSquareSum, ht] at hupper
    change 5 * (∑ B, a B ^ 2) ≤ 225 at hupper
    rw [hsquare] at hupper
    omega

  have haffine : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B := by
    intro B
    simpa [a, ht] using
      E.directionProfile_mul_localGram (G := G) hG c hc u B
  have htrade : localIncidenceMatrix G x *ᵥ a = 0 :=
    affineLocalGramProfile_mul_incidence_of_centroid_zero
      G hG x a hsum_a haffine
  have ha_fun : a = p - n := by
    funext B
    exact ha_eq B
  have hMpMn : localIncidenceMatrix G x *ᵥ p =
      localIncidenceMatrix G x *ᵥ n := by
    rw [ha_fun, Matrix.mulVec_sub] at htrade
    exact sub_eq_zero.mp htrade
  let d : FirstSubconstituent G x → ℤ :=
    localIncidenceMatrix G x *ᵥ p
  have hd_nonneg (z : FirstSubconstituent G x) : 0 ≤ d z := by
    simp only [d, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_nonneg
    intro B _
    have hM : 0 ≤ localIncidenceMatrix G x z B := by
      by_cases hzB : G.Adj (z : V) (B : V) <;>
        simp [localIncidenceMatrix, hzB]
    exact mul_nonneg hM (hp_nonneg B)
  have hd_sum : ∑ z, d z = 9 * q := by
    calc
      ∑ z, d z =
          ∑ z, ∑ B, localIncidenceMatrix G x z B * p B := by
        simp only [d, Matrix.mulVec_apply_eq_sum]
      _ = ∑ B, p B * ∑ z, localIncidenceMatrix G x z B := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro B _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = ∑ B, p B * 9 := by
        apply Finset.sum_congr rfl
        intro B _
        rw [localIncidenceMatrix_column_sum G hG x B]
      _ = (∑ B, p B) * 9 := by
        rw [Finset.sum_mul]
      _ = 9 * q := by
        simp only [q]
        ring

  let T : ℤ := ∑ z, d z ^ 2
  have hcauchyQ :
      ((∑ z, (d z : ℚ)) ^ 2 ≤
        (45 : ℚ) * ∑ z, (d z : ℚ) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (FirstSubconstituent G x)))
      (f := fun z => (d z : ℚ))
    simpa [firstSubconstituent_card G hG x] using h
  have hcauchy : (∑ z, d z) ^ 2 ≤ 45 * T := by
    exact_mod_cast hcauchyQ
  have hT_lower : 9 * q ^ 2 ≤ 5 * T := by
    rw [hd_sum] at hcauchy
    nlinarith

  have hT_cross :
      T = ∑ B, p B * ∑ C, localIntersectionMatrix G x B C * n C := by
    let M := localIncidenceMatrix G x
    calc
      T = d ⬝ᵥ d := by simp [T, dotProduct, pow_two]
      _ = (M *ᵥ n) ⬝ᵥ (M *ᵥ p) := by
        simp only [d, M]
        rw [hMpMn]
      _ = p ⬝ᵥ Mᵀ *ᵥ (M *ᵥ n) := by
        symm
        exact Matrix.dotProduct_transpose_mulVec M p (M *ᵥ n)
      _ = p ⬝ᵥ (Mᵀ * M) *ᵥ n := by
        rw [Matrix.mulVec_mulVec]
      _ = p ⬝ᵥ localIntersectionMatrix G x *ᵥ n := by rfl
      _ = ∑ B, p B * ∑ C,
          localIntersectionMatrix G x B C * n C := by
        simp only [dotProduct, Matrix.mulVec_apply_eq_sum]

  have hadjacency (B : SecondSubconstituent G x) :
      ∑ C, localAdjacencyMatrix G x B C * a C = -12 * a B := by
    have h := affineLocalGramProfile_mul_adjacency
      G hG x a 0 (by simpa using hsum_a)
        (by simpa using haffine) B
    rw [Matrix.vecMul_apply_eq_sum] at h
    have hsym :
        (∑ C, a C * localAdjacencyMatrix G x C B) =
          ∑ C, localAdjacencyMatrix G x B C * a C := by
      apply Finset.sum_congr rfl
      intro C _
      simp [localAdjacencyMatrix, SimpleGraph.adj_comm, mul_comm]
    rw [hsym] at h
    omega

  let A : ℤ :=
    ∑ B, p B * ∑ C, localAdjacencyMatrix G x B C * n C
  have hA_row (B : SecondSubconstituent G x) :
      12 * p B ≤ p B * ∑ C, localAdjacencyMatrix G x B C * n C := by
    rcases hacases B with hneg | hzero | hone
    · simp [p, hneg]
    · simp [p, hzero]
    · have hdecomp :
          (∑ C, localAdjacencyMatrix G x B C * a C) =
            (∑ C, localAdjacencyMatrix G x B C * p C) -
              ∑ C, localAdjacencyMatrix G x B C * n C := by
        calc
          ∑ C, localAdjacencyMatrix G x B C * a C =
              ∑ C, localAdjacencyMatrix G x B C * (p C - n C) := by
            apply Finset.sum_congr rfl
            intro C _
            rw [ha_eq]
          _ = _ := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
      have hpp_nonneg :
          0 ≤ ∑ C, localAdjacencyMatrix G x B C * p C := by
        apply Finset.sum_nonneg
        intro C _
        have hH : 0 ≤ localAdjacencyMatrix G x B C := by
          by_cases hBC : G.Adj (B : V) (C : V) <;>
            simp [localAdjacencyMatrix, hBC]
        exact mul_nonneg hH (hp_nonneg C)
      have hrow := hadjacency B
      rw [hdecomp, hone] at hrow
      simp [p, hone]
      linarith
  have hA_lower : 12 * q ≤ A := by
    calc
      12 * q = ∑ B, 12 * p B := by
        rw [Finset.mul_sum]
      _ ≤ ∑ B, p B * ∑ C,
          localAdjacencyMatrix G x B C * n C :=
        Finset.sum_le_sum fun B _ => hA_row B
      _ = A := rfl

  have hinter_upper (B C : SecondSubconstituent G x) :
      p B * localIntersectionMatrix G x B C * n C ≤
        3 * p B * n C -
          3 * p B * localAdjacencyMatrix G x B C * n C := by
    rcases hacases B with hBneg | hBzero | hBone
    · simp [p, hBneg]
    · simp [p, hBzero]
    · rcases hacases C with hCneg | hCzero | hCone
      · have hne : B ≠ C := by
          intro hBC
          subst C
          omega
        by_cases hBC : (secondSubconstituentGraph G x).Adj B C
        · have hzero := localIntersectionMatrix_of_adj G hG x hBC
          have hAdj : G.Adj (B : V) (C : V) := by
            exact hBC
          simp [p, n, hBone, hCneg, hzero, localAdjacencyMatrix, hAdj]
        · have hcap := blockIntersection_le_three G hG x hne
          have hS : localIntersectionMatrix G x B C ≤ 3 := by
            rw [localIntersectionMatrix_apply]
            exact_mod_cast hcap
          have hNotAdj : ¬G.Adj (B : V) (C : V) := by
            exact hBC
          simp [p, n, hBone, hCneg, localAdjacencyMatrix, hNotAdj]
          exact hS
      · simp [n, hCzero]
      · simp [n, hCone]
  have hT_upper_raw : T ≤ 3 * q * q - 3 * A := by
    rw [hT_cross]
    calc
      (∑ B, p B * ∑ C, localIntersectionMatrix G x B C * n C) =
          ∑ B, ∑ C, p B * localIntersectionMatrix G x B C * n C := by
        apply Finset.sum_congr rfl
        intro B _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        ring
      _ ≤ ∑ B, ∑ C,
          (3 * p B * n C -
            3 * p B * localAdjacencyMatrix G x B C * n C) :=
        Finset.sum_le_sum fun B _ =>
          Finset.sum_le_sum fun C _ => hinter_upper B C
      _ = 3 * q * q - 3 * A := by
        have hfirst :
            (∑ B, ∑ C, 3 * p B * n C) = 3 * q * q := by
          calc
            ∑ B, ∑ C, 3 * p B * n C =
                ∑ B, (3 * p B) * (∑ C, n C) := by
              apply Finset.sum_congr rfl
              intro B _
              rw [Finset.mul_sum]
            _ = (∑ B, 3 * p B) * (∑ C, n C) := by
              rw [Finset.sum_mul]
            _ = 3 * (∑ B, p B) * (∑ C, n C) := by
              have hp3 : ∑ B, 3 * p B = 3 * ∑ B, p B := by
                rw [Finset.mul_sum]
              rw [hp3]
            _ = 3 * q * q := by
              simp only [q]
              rw [hsum_pn]
        have hsecond :
            (∑ B, ∑ C,
              3 * p B * localAdjacencyMatrix G x B C * n C) = 3 * A := by
          dsimp only [A]
          calc
            ∑ B, ∑ C,
                3 * p B * localAdjacencyMatrix G x B C * n C =
                ∑ B, (3 * p B) * ∑ C,
                  localAdjacencyMatrix G x B C * n C := by
              apply Finset.sum_congr rfl
              intro B _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C _
              ring
            _ = 3 * ∑ B, p B * ∑ C,
                localAdjacencyMatrix G x B C * n C := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro B _
              ring
            _ = _ := rfl
        calc
          ∑ B, ∑ C,
              (3 * p B * n C -
                3 * p B * localAdjacencyMatrix G x B C * n C) =
              ∑ B, ((∑ C, 3 * p B * n C) -
                ∑ C, 3 * p B * localAdjacencyMatrix G x B C * n C) := by
            apply Finset.sum_congr rfl
            intro B _
            rw [Finset.sum_sub_distrib]
          _ = (∑ B, ∑ C, 3 * p B * n C) -
              ∑ B, ∑ C,
                3 * p B * localAdjacencyMatrix G x B C * n C := by
            rw [Finset.sum_sub_distrib]
          _ = 3 * q * q - 3 * A := by rw [hfirst, hsecond]
  have hT_upper : T ≤ 3 * q * q - 36 * q := by
    nlinarith [hA_lower, hT_upper_raw]
  have hq_zero : q = 0 := by
    by_contra hq
    have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq)
    have hq_ge : 30 ≤ q := by
      nlinarith [hT_lower, hT_upper]
    omega
  have hpB₀ : p B₀ = 0 := by
    have hsingle : p B₀ ≤ ∑ B, p B :=
      Finset.single_le_sum
        (fun B _ => hp_nonneg B) (Finset.mem_univ B₀)
    have hq_def : ∑ B, p B = q := rfl
    rw [hq_def, hq_zero] at hsingle
    have hnonneg := hp_nonneg B₀
    omega
  have hnB₀ : n B₀ = 0 := by
    have hsingle : n B₀ ≤ ∑ B, n B :=
      Finset.single_le_sum
        (fun B _ => hn_nonneg B) (Finset.mem_univ B₀)
    have hq_def : ∑ B, p B = q := rfl
    have hn_sum_zero : ∑ B, n B = 0 := by
      rw [← hsum_pn, hq_def, hq_zero]
    rw [hn_sum_zero] at hsingle
    have hnonneg := hn_nonneg B₀
    omega
  change a B₀ = 0
  rw [ha_eq, hpB₀, hnB₀]
  norm_num

end Rank15EmbeddingWitness

end SRG266
