/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.NormOneDirections

/-!
# Extremal norm-one directions produce a Delsarte coclique

The local block-intersection algebra sharpens the centroid coordinate of a
norm-one host direction to `-5`, `0`, or `5`.  This file eliminates the two
extremal values without any host classification or shell enumeration.

At centroid coordinate five, the ternary direction profile has sum and
squared sum both equal to 55.  It is therefore the characteristic function
of a 55-set.  Its affine adjacency equation says that this set is independent
in the second subconstituent.  Adding the root gives a size-56 coclique in the
original graph, hence the forbidden quasi-symmetric design.
-/

open scoped Matrix

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Rank15EmbeddingWitness

/-- The positive support of a host direction on the distinguished local Gram
generators. -/
def positiveDirectionSupport
    {x : V} (E : Rank15EmbeddingWitness G x) (u : E.host.carrier) :
    Finset (SecondSubconstituent G x) :=
  Finset.univ.filter fun B => E.directionProfile (G := G) u B = 1

/-- At the positive extremal centroid coordinate, every profile entry is
zero or one. -/
theorem directionProfile_zero_or_one_of_centroid_eq_five
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (ht : E.centroidCoordinate (G := G) c u = 5)
    (B : SecondSubconstituent G x) :
    E.directionProfile (G := G) u B = 0 ∨
      E.directionProfile (G := G) u B = 1 := by
  let a : SecondSubconstituent G x → ℤ :=
    E.directionProfile (G := G) u
  have hsum : ∑ C, a C = 55 := by
    simpa [a, ht] using E.directionProfile_sum (G := G) c hc u
  have hupper : 5 * ∑ C, a C ^ 2 ≤ 275 := by
    have h := E.directionProfile_upper_bound (G := G) hG c hc u hu
    simpa [directionSquareSum, a, ht] using h
  have hdiff_nonneg (C : SecondSubconstituent G x) :
      0 ≤ a C ^ 2 - a C := by
    rcases E.directionProfile_cases (G := G) hG u hu C with
      hneg | hzero | hone
    · simp [a, hneg]
    · simp [a, hzero]
    · simp [a, hone]
  have hsingle :
      a B ^ 2 - a B ≤ ∑ C, (a C ^ 2 - a C) := by
    exact Finset.single_le_sum
      (fun C _ => hdiff_nonneg C) (Finset.mem_univ B)
  have hdiff_sum : ∑ C, (a C ^ 2 - a C) ≤ 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    omega
  rcases E.directionProfile_cases (G := G) hG u hu B with
    hneg | hzero | hone
  · change a B = -1 at hneg
    rw [hneg] at hsingle
    omega
  · exact Or.inl hzero
  · exact Or.inr hone

/-- The positive extremal profile has support 55. -/
theorem positiveDirectionSupport_card_of_centroid_eq_five
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (ht : E.centroidCoordinate (G := G) c u = 5) :
    (E.positiveDirectionSupport (G := G) u).card = 55 := by
  let a : SecondSubconstituent G x → ℤ :=
    E.directionProfile (G := G) u
  have hsum : ∑ B, a B = 55 := by
    simpa [a, ht] using E.directionProfile_sum (G := G) c hc u
  have hentries :
      (∑ B, a B) = ∑ B, if a B = 1 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro B _
    rcases E.directionProfile_zero_or_one_of_centroid_eq_five
        (G := G) hG c hc u hu ht B with hzero | hone
    · simp [a, hzero]
    · simp [a, hone]
  have hcard :
      (∑ B, if a B = 1 then (1 : ℤ) else 0) =
        ((E.positiveDirectionSupport (G := G) u).card : ℤ) := by
    simp [positiveDirectionSupport, a,
      (Finset.sum_boole
        (R := ℤ)
        (fun B : SecondSubconstituent G x => a B = 1)
        Finset.univ)]
  have hcard' :
      ((E.positiveDirectionSupport (G := G) u).card : ℤ) = 55 :=
    hcard.symm.trans (hentries.symm.trans hsum)
  exact_mod_cast hcard'

/-- The positive extremal support is independent in the second
subconstituent. -/
theorem positiveDirectionSupport_isIndepSet_of_centroid_eq_five
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (ht : E.centroidCoordinate (G := G) c u = 5) :
    (secondSubconstituentGraph G x).IsIndepSet
      (E.positiveDirectionSupport (G := G) u :
        Set (SecondSubconstituent G x)) := by
  let a : SecondSubconstituent G x → ℤ :=
    E.directionProfile (G := G) u
  have hsum : ∑ B, a B = 11 * 5 := by
    simpa [a, ht] using E.directionProfile_sum (G := G) c hc u
  have haffine : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B + 6 * 5 := by
    intro B
    simpa [a, ht] using
      E.directionProfile_mul_localGram (G := G) hG c hc u B
  rw [SimpleGraph.isIndepSet_iff]
  intro B hB C hC _hne hBC
  have hBone : a B = 1 := by
    exact (Finset.mem_filter.mp hB).2
  have hCone : a C = 1 := by
    exact (Finset.mem_filter.mp hC).2
  have hadj := affineLocalGramProfile_mul_adjacency
    G hG x a 5 hsum haffine B
  have htotal :
      ∑ D, a D * localAdjacencyMatrix G x D B = 0 := by
    rw [Matrix.vecMul_apply_eq_sum] at hadj
    rw [hBone] at hadj
    omega
  have hnonneg :
      ∀ D ∈ (Finset.univ : Finset (SecondSubconstituent G x)),
        0 ≤ a D * localAdjacencyMatrix G x D B := by
    intro D _
    have haD : 0 ≤ a D := by
      rcases E.directionProfile_zero_or_one_of_centroid_eq_five
          (G := G) hG c hc u hu ht D with hzero | hone
      · simp [a, hzero]
      · simp [a, hone]
    have hH : 0 ≤ localAdjacencyMatrix G x D B := by
      by_cases hDB : G.Adj (D : V) (B : V) <;>
        simp [localAdjacencyMatrix, hDB]
    exact mul_nonneg haD hH
  have hsingle :
      a C * localAdjacencyMatrix G x C B ≤
        ∑ D, a D * localAdjacencyMatrix G x D B :=
    Finset.single_le_sum hnonneg (Finset.mem_univ C)
  have hterm : a C * localAdjacencyMatrix G x C B = 1 := by
    change G.Adj (B : V) (C : V) at hBC
    rw [hCone]
    simp [localAdjacencyMatrix, hBC.symm]
  rw [hterm, htotal] at hsingle
  omega

/-- A positive extremal norm-one direction produces a global Delsarte
coclique. -/
theorem exists_global_coclique_of_centroidCoordinate_eq_five
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (ht : E.centroidCoordinate (G := G) c u = 5) :
    ∃ C : Finset V, C.card = 56 ∧ G.IsIndepSet (C : Set V) := by
  let S := E.positiveDirectionSupport (G := G) u
  refine ⟨extendSecondCoclique G x S, ?_, ?_⟩
  · rw [extendSecondCoclique_card]
    rw [E.positiveDirectionSupport_card_of_centroid_eq_five
      (G := G) hG c hc u hu ht]
  · apply extendSecondCoclique_isIndepSet G x S
    exact E.positiveDirectionSupport_isIndepSet_of_centroid_eq_five
      (G := G) hG c hc u hu ht

/-- Conditional only on the named design theorem, the centroid coordinate of
every norm-one host direction is zero. -/
theorem centroidCoordinate_eq_zero_of_noQuasiSymmetricDesign
    {x : V} (E : Rank15EmbeddingWitness G x)
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    E.centroidCoordinate (G := G) c u = 0 := by
  rcases E.centroidCoordinate_cases_sharp (G := G) hG c hc u hu with
    hneg | hzero | hpos
  · have hnegNorm : E.host.pairing (-u) (-u) = 1 := by
      simpa using hu
    have hnegCoord : E.centroidCoordinate (G := G) c (-u) = 5 := by
      have h := congrArg Neg.neg hneg
      simpa [centroidCoordinate, embeddedCentroid] using h
    obtain ⟨C, hCcard, hC⟩ :=
      E.exists_global_coclique_of_centroidCoordinate_eq_five
        (G := G) hG c hc (-u) hnegNorm hnegCoord
    exact (hMT.false
      (cocliqueQuasiSymmetricDesign G hG C hCcard hC)).elim
  · exact hzero
  · obtain ⟨C, hCcard, hC⟩ :=
      E.exists_global_coclique_of_centroidCoordinate_eq_five
        (G := G) hG c hc u hu hpos
    exact (hMT.false
      (cocliqueQuasiSymmetricDesign G hG C hCcard hC)).elim

end Rank15EmbeddingWitness

end SRG266
