/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.ExternalLatticeInputs
import SRG266.KernelReduction

/-!
# Norm-one directions in a rank-15 host

This file develops the graph-specific algebra needed to separate norm-one
summands of an odd unimodular rank-15 host.  It does not classify such hosts.
Instead, it turns every norm-one host vector into an exact integral profile on
the 220 distinguished local Gram generators.

The first ingredient is the frame identity in the abstract quotient lattice.
It is proved before choosing host coordinates, so every later mixed-shell
reduction can reuse the same kernel-checked statement.

The second ingredient is the projector bound.  `directionSquareSum_le'` is
stated for an arbitrary host direction and carries its norm, so it applies to
lattice vectors of norm larger than one; `directionSquareSum_sum_le` is its
sum over a finite family, and `directionProfile_upper_bound` is the unit-norm
specialization used by the mixed-shell audit below.
-/

open scoped Matrix

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Pairings with the distinguished generators separate points of the
abstract integral Gram lattice. -/
theorem integralGram_eq_of_pairing_generators_eq
    (x : V) (p q : IntegralGramLattice G x)
    (h : ∀ B : SecondSubconstituent G x,
      integralGramPairing G x p (integralGramGenerator G x B) =
        integralGramPairing G x q (integralGramGenerator G x B)) :
    p = q := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
    (integralGramRelations G x) p
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
    (integralGramRelations G x) q
  apply (Submodule.Quotient.eq (integralGramRelations G x)).2
  rw [integralGramRelations, LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change Matrix.toBilin' (localGramMatrix G x) (a - b) y = 0
  rw [Matrix.toBilin'_apply]
  calc
    (∑ i, ∑ j, (a - b) i * localGramMatrix G x i j * y j) =
        ∑ j, y j * ∑ i, (a i - b i) * localGramMatrix G x i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply]
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro B _
      have hB := h B
      change
        Matrix.toBilin' (localGramMatrix G x) a (Pi.single B 1) =
          Matrix.toBilin' (localGramMatrix G x) b (Pi.single B 1) at hB
      have hcolumn :
          ∑ C, (a C - b C) * localGramMatrix G x C B = 0 := by
        simpa [Matrix.toBilin'_apply, Pi.single_apply, sub_mul] using
          sub_eq_zero.mpr hB
      rw [hcolumn, mul_zero]

/-- The projector/frame identity in the abstract integral Gram lattice.  This
is the coordinate-free form of `L² = 45L + 90J`, with `11c = ∑ v_B`. -/
theorem integralGram_frame_identity
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    (∑ C, localGramMatrix G x C B • integralGramGenerator G x C) =
      (45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c := by
  apply integralGram_eq_of_pairing_generators_eq G x
  intro D
  simp only [map_sum, LinearMap.sum_apply, map_add,
    LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
    integralGramPairing_generator_generator G x]
  rw [integral_centroid_pairing_generator G hG x c hc D]
  have hsq := localGramMatrix_sq_apply G hG x D B
  change
    (∑ C, localGramMatrix G x C B * localGramMatrix G x C D) =
      45 * localGramMatrix G x B D + 6 * 15
  calc
    (∑ C, localGramMatrix G x C B * localGramMatrix G x C D) =
        (localGramMatrix G x * localGramMatrix G x) D B := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro C _
      rw [localGramMatrix_comm G x C B,
        localGramMatrix_comm G x C D]
      ring
    _ = 45 * localGramMatrix G x D B + 90 := hsq
    _ = 45 * localGramMatrix G x B D + 6 * 15 := by
      rw [localGramMatrix_comm G x D B]
      ring

namespace Rank15EmbeddingWitness

/-- A distinguished local Gram generator viewed in the rank-15 host. -/
def embeddedGenerator (E : Rank15EmbeddingWitness G x)
    (B : SecondSubconstituent G x) : E.host.carrier :=
  E.embedding (integralGramGenerator G x B)

/-- An integral centroid viewed in the rank-15 host. -/
def embeddedCentroid (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x) : E.host.carrier :=
  E.embedding c

/-- The integral coefficient profile cut out by a host vector. -/
def directionProfile (E : Rank15EmbeddingWitness G x)
    (u : E.host.carrier) (B : SecondSubconstituent G x) : ℤ :=
  E.host.pairing u (E.embeddedGenerator (G := G) B)

/-- The coordinate of an embedded centroid in a host direction. -/
def centroidCoordinate (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x) (u : E.host.carrier) : ℤ :=
  E.host.pairing u (E.embeddedCentroid (G := G) c)

@[simp]
theorem embeddedGenerator_pairing
    (E : Rank15EmbeddingWitness G x)
    (B C : SecondSubconstituent G x) :
    E.host.pairing (E.embeddedGenerator (G := G) B)
        (E.embeddedGenerator (G := G) C) = localGramMatrix G x B C := by
  rw [embeddedGenerator, embeddedGenerator, E.preservesPairing,
    integralGramPairing_generator_generator]

theorem embeddedGenerator_norm
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (B : SecondSubconstituent G x) :
    E.host.pairing (E.embeddedGenerator (G := G) B)
        (E.embeddedGenerator (G := G) B) = 3 := by
  rw [embeddedGenerator_pairing (G := G) E,
    localGramMatrix_diagonal G hG x B]

theorem embeddedCentroid_pairing_generator
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    E.host.pairing (E.embeddedCentroid (G := G) c)
        (E.embeddedGenerator (G := G) B) = 15 := by
  rw [embeddedCentroid, embeddedGenerator, E.preservesPairing,
    integral_centroid_pairing_generator G hG x c hc B]

theorem embeddedCentroid_norm
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    E.host.pairing (E.embeddedCentroid (G := G) c)
        (E.embeddedCentroid (G := G) c) = 300 := by
  rw [embeddedCentroid, E.preservesPairing,
    integral_centroid_norm G hG x c hc]

end Rank15EmbeddingWitness

/-- A norm-one vector has coefficient `-1`, `0`, or `1` against every
norm-three vector in a positive-definite integral lattice. -/
theorem OddUnimodularLattice15.pairing_normOne_normThree_cases
    (host : OddUnimodularLattice15)
    (u v : host.carrier)
    (hu : host.pairing u u = 1)
    (hv : host.pairing v v = 3) :
    host.pairing u v = -1 ∨
      host.pairing u v = 0 ∨ host.pairing u v = 1 := by
  let a : ℤ := host.pairing u v
  let w : host.carrier := a • u - v
  have hw_nonneg : 0 ≤ host.pairing w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (host.positiveDefinite w hw).le
  have hva : host.pairing v u = a := by
    rw [host.symmetric.eq v u]
  have hw_norm : host.pairing w w = 3 - a * a := by
    have huu : host.pairing (a • u) (a • u) = a * a := by
      simp [hu]
    have huv : host.pairing (a • u) v = a * a := by
      simp [a]
    have hvu : host.pairing v (a • u) = a * a := by
      simp [hva]
    simp only [w, map_sub, LinearMap.sub_apply]
    rw [huu, huv, hvu, hv]
    ring
  rw [hw_norm] at hw_nonneg
  have ha_lower : -2 < a := by
    by_contra h
    have ha : a ≤ -2 := by omega
    nlinarith
  have ha_upper : a < 2 := by
    by_contra h
    have ha : 2 ≤ a := by omega
    nlinarith
  change a = -1 ∨ a = 0 ∨ a = 1
  omega

/-- Every norm-one host direction therefore gives a ternary profile on the
220 local Gram generators. -/
theorem Rank15EmbeddingWitness.directionProfile_cases
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1)
    (B : SecondSubconstituent G x) :
    E.directionProfile (G := G) u B = -1 ∨
      E.directionProfile (G := G) u B = 0 ∨
        E.directionProfile (G := G) u B = 1 := by
  exact E.host.pairing_normOne_normThree_cases u
    (E.embeddedGenerator (G := G) B) hu
      (E.embeddedGenerator_norm (G := G) hG B)

/-- The embedded centroid relation, before applying a host coordinate. -/
theorem Rank15EmbeddingWitness.sum_embeddedGenerator
    (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    (∑ B, E.embeddedGenerator (G := G) B) =
      E.embedding ((11 : ℤ) • c) := by
  have h := congrArg E.embedding hc
  simpa [integralGramGeneratorSum, embeddedGenerator] using h.symm

/-- The signed sum of a norm-one direction profile is eleven times its
centroid coordinate. -/
theorem Rank15EmbeddingWitness.directionProfile_sum
    (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier) :
    (∑ B, E.directionProfile (G := G) u B) =
      11 * E.centroidCoordinate (G := G) c u := by
  let f : IntegralGramLattice G x →ₗ[ℤ] ℤ :=
    (E.host.pairing u).comp E.embedding
  have h := congrArg f hc
  simpa [f, integralGramGeneratorSum, directionProfile,
    centroidCoordinate, embeddedGenerator, embeddedCentroid] using h.symm

/-- The abstract frame identity transported to an arbitrary rank-15 host. -/
theorem Rank15EmbeddingWitness.embedded_frame_identity
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    (∑ C, E.embedding (localGramMatrix G x C B •
        integralGramGenerator G x C)) =
      E.embedding ((45 : ℤ) • integralGramGenerator G x B +
        (6 : ℤ) • c) := by
  have h := congrArg E.embedding
    (integralGram_frame_identity G hG x c hc B)
  simpa using h

/-- Every host direction profile satisfies the same affine `L`-eigenvector
equation.  No host classification enters this identity. -/
theorem Rank15EmbeddingWitness.directionProfile_mul_localGram
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (B : SecondSubconstituent G x) :
    (∑ C, E.directionProfile (G := G) u C *
        localGramMatrix G x C B) =
      45 * E.directionProfile (G := G) u B +
        6 * E.centroidCoordinate (G := G) c u := by
  let f : IntegralGramLattice G x →ₗ[ℤ] ℤ :=
    (E.host.pairing u).comp E.embedding
  have h := congrArg f
    (integralGram_frame_identity G hG x c hc B)
  simpa [f, directionProfile, centroidCoordinate, embeddedCentroid,
    embeddedGenerator, mul_comm] using h

/-- The squared ℓ² size of a host direction profile.  For a norm-one
direction this is also the number of nonzero profile entries. -/
def Rank15EmbeddingWitness.directionSquareSum
    (E : Rank15EmbeddingWitness G x) (u : E.host.carrier) : ℤ :=
  ∑ B, E.directionProfile (G := G) u B ^ 2

/-- Cauchy--Schwarz against the norm-300 centroid, proved integrally from
positive definiteness. -/
theorem Rank15EmbeddingWitness.centroidCoordinate_sq_le
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    E.centroidCoordinate (G := G) c u ^ 2 ≤ 300 := by
  let t : ℤ := E.centroidCoordinate (G := G) c u
  let z : E.host.carrier := t • u - E.embeddedCentroid (G := G) c
  have hz_nonneg : 0 ≤ E.host.pairing z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (E.host.positiveDefinite z hz).le
  have hcu :
      E.host.pairing (E.embeddedCentroid (G := G) c) u = t := by
    rw [E.host.symmetric.eq]
    rfl
  have hzz : E.host.pairing z z = 300 - t * t := by
    have huu : E.host.pairing (t • u) (t • u) = t * t := by
      simp [hu]
    have huc :
        E.host.pairing (t • u) (E.embeddedCentroid (G := G) c) =
          t * t := by
      simp [t, centroidCoordinate]
    have hcu' :
        E.host.pairing (E.embeddedCentroid (G := G) c) (t • u) =
          t * t := by
      simp [hcu]
    simp only [z, map_sub, LinearMap.sub_apply]
    rw [huu, huc, hcu', E.embeddedCentroid_norm (G := G) hG c hc]
    ring
  rw [hzz] at hz_nonneg
  change t ^ 2 ≤ 300
  nlinarith

/-- The signed-sum equation and ternary entries force the elementary lower
bound `11 |t| ≤ ∑ a_B²`. -/
theorem Rank15EmbeddingWitness.directionProfile_lower_bound
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    11 * |E.centroidCoordinate (G := G) c u| ≤
      E.directionSquareSum (G := G) u := by
  let a : SecondSubconstituent G x → ℤ :=
    E.directionProfile (G := G) u
  let t : ℤ := E.centroidCoordinate (G := G) c u
  have ha_abs (B : SecondSubconstituent G x) : |a B| = a B ^ 2 := by
    rcases E.directionProfile_cases (G := G) hG u hu B with
      hneg | hzero | hone
    · simp [a, hneg]
    · simp [a, hzero]
    · simp [a, hone]
  have hsum : ∑ B, a B = 11 * t := by
    simpa [a, t] using E.directionProfile_sum (G := G) c hc u
  calc
    11 * |t| = |11 * t| := by simp
    _ = |∑ B, a B| := by rw [hsum]
    _ ≤ ∑ B, |a B| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ B, a B ^ 2 := by
      apply Finset.sum_congr rfl
      intro B _
      exact ha_abs B
    _ = E.directionSquareSum (G := G) u := rfl

/-- The host-space frame vector associated with a direction profile. -/
def Rank15EmbeddingWitness.directionFrame
    (E : Rank15EmbeddingWitness G x) (u : E.host.carrier) : E.host.carrier :=
  ∑ B, E.directionProfile (G := G) u B •
    E.embeddedGenerator (G := G) B

theorem Rank15EmbeddingWitness.pairing_direction_directionFrame
    (E : Rank15EmbeddingWitness G x)
    (u : E.host.carrier) :
    E.host.pairing u (E.directionFrame (G := G) u) =
      E.directionSquareSum (G := G) u := by
  simp only [directionFrame, map_sum, map_zsmul,
    directionSquareSum, directionProfile, zsmul_eq_mul, Int.cast_id,
    pow_two]

theorem Rank15EmbeddingWitness.pairing_generator_directionFrame
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (B : SecondSubconstituent G x) :
    E.host.pairing (E.embeddedGenerator (G := G) B)
        (E.directionFrame (G := G) u) =
      45 * E.directionProfile (G := G) u B +
        6 * E.centroidCoordinate (G := G) c u := by
  rw [directionFrame, map_sum]
  simp only [map_zsmul, zsmul_eq_mul,
    embeddedGenerator_pairing, Int.cast_id]
  calc
    (∑ C, E.directionProfile (G := G) u C *
        localGramMatrix G x B C) =
        ∑ C, E.directionProfile (G := G) u C *
          localGramMatrix G x C B := by
      apply Finset.sum_congr rfl
      intro C _
      rw [localGramMatrix_comm G x B C]
    _ = _ := E.directionProfile_mul_localGram
      (G := G) hG c hc u B

theorem Rank15EmbeddingWitness.pairing_centroid_directionFrame
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier) :
    E.host.pairing (E.embeddedCentroid (G := G) c)
        (E.directionFrame (G := G) u) =
      165 * E.centroidCoordinate (G := G) c u := by
  rw [directionFrame, map_sum]
  simp only [map_zsmul, zsmul_eq_mul,
    E.embeddedCentroid_pairing_generator (G := G) hG c hc,
    Int.cast_id]
  rw [← Finset.sum_mul, E.directionProfile_sum (G := G) c hc u]
  ring

theorem Rank15EmbeddingWitness.directionFrame_norm
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier) :
    E.host.pairing (E.directionFrame (G := G) u)
        (E.directionFrame (G := G) u) =
      45 * E.directionSquareSum (G := G) u +
        66 * E.centroidCoordinate (G := G) c u ^ 2 := by
  rw [directionFrame, map_sum]
  simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
  calc
    (∑ B, E.directionProfile (G := G) u B *
        E.host.pairing (E.directionFrame (G := G) u)
          (E.embeddedGenerator (G := G) B)) =
        ∑ B, E.directionProfile (G := G) u B *
          (45 * E.directionProfile (G := G) u B +
            6 * E.centroidCoordinate (G := G) c u) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [E.host.symmetric.eq]
      rw [E.pairing_generator_directionFrame (G := G) hG c hc u B]
    _ = 45 * E.directionSquareSum (G := G) u +
        66 * E.centroidCoordinate (G := G) c u ^ 2 := by
      calc
        (∑ B, E.directionProfile (G := G) u B *
            (45 * E.directionProfile (G := G) u B +
              6 * E.centroidCoordinate (G := G) c u)) =
            ∑ B, (45 * E.directionProfile (G := G) u B ^ 2 +
              6 * E.centroidCoordinate (G := G) c u *
                E.directionProfile (G := G) u B) := by
          apply Finset.sum_congr rfl
          intro B _
          ring
        _ = 45 * (∑ B, E.directionProfile (G := G) u B ^ 2) +
            6 * E.centroidCoordinate (G := G) c u *
              (∑ B, E.directionProfile (G := G) u B) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
        _ = _ := by
          rw [E.directionProfile_sum (G := G) c hc u]
          simp only [directionSquareSum]
          ring

/-- The integral numerator of the orthogonal projection of a host direction
onto the local Gram span. -/
def Rank15EmbeddingWitness.directionProjectorNumerator
    (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x) (u : E.host.carrier) : E.host.carrier :=
  (5 : ℤ) • E.directionFrame (G := G) u -
    (2 * E.centroidCoordinate (G := G) c u) •
      E.embeddedCentroid (G := G) c

theorem Rank15EmbeddingWitness.pairing_direction_projectorNumerator
    (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x)
    (u : E.host.carrier) :
    E.host.pairing u (E.directionProjectorNumerator (G := G) c u) =
      5 * E.directionSquareSum (G := G) u -
        2 * E.centroidCoordinate (G := G) c u ^ 2 := by
  simp only [directionProjectorNumerator, map_sub, map_zsmul,
    zsmul_eq_mul, Int.cast_id,
    E.pairing_direction_directionFrame (G := G), centroidCoordinate]
  ring

theorem Rank15EmbeddingWitness.directionProjectorNumerator_norm
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier) :
    E.host.pairing (E.directionProjectorNumerator (G := G) c u)
        (E.directionProjectorNumerator (G := G) c u) =
      225 * (5 * E.directionSquareSum (G := G) u -
        2 * E.centroidCoordinate (G := G) c u ^ 2) := by
  let F := E.directionFrame (G := G) u
  let C := E.embeddedCentroid (G := G) c
  let t := E.centroidCoordinate (G := G) c u
  have hFF : E.host.pairing F F =
      45 * E.directionSquareSum (G := G) u + 66 * t ^ 2 := by
    simpa [F, t] using E.directionFrame_norm (G := G) hG c hc u
  have hCF : E.host.pairing C F = 165 * t := by
    simpa [C, F, t] using
      E.pairing_centroid_directionFrame (G := G) hG c hc u
  have hFC : E.host.pairing F C = 165 * t := by
    rw [E.host.symmetric.eq]
    exact hCF
  have hCC : E.host.pairing C C = 300 := by
    simpa [C] using E.embeddedCentroid_norm (G := G) hG c hc
  change E.host.pairing (5 • F - (2 * t) • C)
      (5 • F - (2 * t) • C) = _
  simp only [map_sub, LinearMap.sub_apply, map_zsmul,
    LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
  rw [hFF, hFC, hCF, hCC]
  ring

/-- The diagonal bound for the local row-space projector at an *arbitrary*
host direction: the norm-one hypothesis of
`Rank15EmbeddingWitness.directionProfile_upper_bound` is dropped and the host
norm `⟨y, y⟩` is carried instead.

Geometrically this is `‖P_W y‖² ≤ ‖y‖²` for the orthogonal projector `P_W`
onto the rational span of the embedded local Gram lattice, cleared of all
denominators: with `N(y) := 5 • F(y) - 2 t(y) • c` one has
`⟨y, N(y)⟩ = 5 S(y) - 2 t(y)²` and `⟨N(y), N(y)⟩ = 225 (5 S(y) - 2 t(y)²)`,
so positive definiteness applied to `225 • y - N(y)` gives
`0 ≤ 225 * (225 * ⟨y, y⟩ - (5 * S(y) - 2 * t(y)²))`.

This is the form every host-classification branch uses: the sharp constants
are obtained by evaluating it at explicit lattice vectors of norm bigger than
one (`2 e_j ∈ D12` and `8 e_i - 1 ∈ A7 ⊂ E7`), where the unit-norm version is
silent. -/
theorem Rank15EmbeddingWitness.directionSquareSum_le'
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (y : E.host.carrier) :
    5 * E.directionSquareSum (G := G) y ≤
      225 * E.host.pairing y y +
        2 * E.centroidCoordinate (G := G) c y ^ 2 := by
  let N := E.directionProjectorNumerator (G := G) c y
  let z : E.host.carrier := (225 : ℤ) • y - N
  have hz_nonneg : 0 ≤ E.host.pairing z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (E.host.positiveDefinite z hz).le
  have hyN : E.host.pairing y N =
      5 * E.directionSquareSum (G := G) y -
        2 * E.centroidCoordinate (G := G) c y ^ 2 := by
    simpa [N] using E.pairing_direction_projectorNumerator (G := G) c y
  have hNy : E.host.pairing N y =
      5 * E.directionSquareSum (G := G) y -
        2 * E.centroidCoordinate (G := G) c y ^ 2 := by
    rw [E.host.symmetric.eq]
    exact hyN
  have hNN : E.host.pairing N N =
      225 * (5 * E.directionSquareSum (G := G) y -
        2 * E.centroidCoordinate (G := G) c y ^ 2) := by
    simpa [N] using
      E.directionProjectorNumerator_norm (G := G) hG c hc y
  have hzz : E.host.pairing z z =
      225 * (225 * E.host.pairing y y -
        (5 * E.directionSquareSum (G := G) y -
          2 * E.centroidCoordinate (G := G) c y ^ 2)) := by
    simp only [z, map_sub, LinearMap.sub_apply, map_zsmul,
      LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
    rw [hyN, hNy, hNN]
    ring
  rw [hzz] at hz_nonneg
  linarith

/-- The summed projector bound over a finite family of host directions.

This is the form the host-classification branches consume.  A single
direction bounds one centroid coordinate from below; the branch conclusions
need the bound to be *tight*, which is only visible after summing over an
explicit family and comparing the total against `⟨c, c⟩ = 300` or against a
trace identity.  Nothing is assumed about the family: it may repeat vectors
and need not be linearly independent, because only the three totals matter. -/
theorem Rank15EmbeddingWitness.directionSquareSum_sum_le
    {ι : Type*} (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (s : Finset ι) (y : ι → E.host.carrier) :
    5 * ∑ i ∈ s, E.directionSquareSum (G := G) (y i) ≤
      225 * ∑ i ∈ s, E.host.pairing (y i) (y i) +
        2 * ∑ i ∈ s, E.centroidCoordinate (G := G) c (y i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    E.directionSquareSum_le' (G := G) hG c hc (y i)

/-- The diagonal bound for the local row-space projector, available for
one norm-one direction without assuming a complete integer factorization.

This is the unit-norm specialization of
`Rank15EmbeddingWitness.directionSquareSum_le'`. -/
theorem Rank15EmbeddingWitness.directionProfile_upper_bound
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    5 * E.directionSquareSum (G := G) u ≤
      225 + 2 * E.centroidCoordinate (G := G) c u ^ 2 := by
  have h := E.directionSquareSum_le' (G := G) hG c hc u
  rwa [hu, mul_one] at h

/-- Every norm-one direction has centroid coordinate of absolute value at
most five.  This is the key finite reduction for mixed unit/core shells. -/
theorem Rank15EmbeddingWitness.centroidCoordinate_abs_le_five
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    |E.centroidCoordinate (G := G) c u| ≤ 5 := by
  exact centroid_coordinate_abs_le_five
    (E.centroidCoordinate (G := G) c u)
    (E.directionSquareSum (G := G) u)
    (by simpa [pow_two] using
      E.centroidCoordinate_sq_le (G := G) hG c hc u hu)
    (E.directionProfile_lower_bound (G := G) hG c hc u hu)
    (by
      have hupper :=
        E.directionProfile_upper_bound (G := G) hG c hc u hu
      simp only [pow_two] at hupper
      nlinarith)

/-- An integral affine `L`-profile remembers more of the original local
design than its Gram equation alone suggests.  Multiplication by the block
intersection matrix gives

`5 (aᵀ S) = 99 t · 1`.

The factor five is the useful part: it rules out four of the eleven a priori
possible centroid coordinates for norm-one directions. -/
theorem affineLocalGramProfile_mul_intersection
    (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) (t : ℤ)
    (hsum : ∑ B, a B = 11 * t)
    (haffine : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B + 6 * t)
    (D : SecondSubconstituent G x) :
    5 * (a ᵥ* localIntersectionMatrix G x) D = 99 * t := by
  have hprofile :
      a ᵥ* localGramMatrix G x = fun B => 45 * a B + 6 * t := by
    funext B
    simpa [Matrix.vecMul_apply_eq_sum] using haffine B
  have hcol : ∑ B, localIntersectionMatrix G x B D = 396 := by
    calc
      ∑ B, localIntersectionMatrix G x B D =
          ∑ B, localIntersectionMatrix G x D B := by
        apply Finset.sum_congr rfl
        intro B _
        exact localIntersectionMatrix_comm G x B D
      _ = 396 := by
        have h := congrFun (localIntersectionMatrix_mulVec_one G hG x) D
        simpa [Matrix.mulVec_apply_eq_sum] using h
  have hassoc := congrFun
    (Matrix.vecMul_vecMul a (localGramMatrix G x)
      (localIntersectionMatrix G x)) D
  rw [hprofile, localGram_mul_intersection G hG x] at hassoc
  simp only [Matrix.vecMul_apply_eq_sum, nsmulMatrix_apply,
    allOnesMatrix_apply, mul_one] at hassoc
  have hleft :
      (∑ B, (45 * a B + 6 * t) * localIntersectionMatrix G x B D) =
        45 * (a ᵥ* localIntersectionMatrix G x) D + 2376 * t := by
    rw [Matrix.vecMul_apply_eq_sum]
    calc
      (∑ B, (45 * a B + 6 * t) * localIntersectionMatrix G x B D) =
          ∑ B, (45 * (a B * localIntersectionMatrix G x B D) +
            (6 * t) * localIntersectionMatrix G x B D) := by
        apply Finset.sum_congr rfl
        intro B _
        ring
      _ = 45 * (∑ B, a B * localIntersectionMatrix G x B D) +
          (6 * t) * (∑ B, localIntersectionMatrix G x B D) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 45 * (∑ B, a B * localIntersectionMatrix G x B D) +
          2376 * t := by
        rw [hcol]
        ring
  have hright : ∑ B, a B * 297 = 3267 * t := by
    calc
      ∑ B, a B * 297 = (∑ B, a B) * 297 := by
        rw [Finset.sum_mul]
      _ = 3267 * t := by rw [hsum]; ring
  norm_num at hassoc
  rw [hleft, hright] at hassoc
  linarith

/-- The same affine profile is an affine `-12` eigenvector for the second
subconstituent adjacency matrix.  The denominator-free form is convenient
over the integers. -/
theorem affineLocalGramProfile_mul_adjacency
    (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) (t : ℤ)
    (hsum : ∑ B, a B = 11 * t)
    (haffine : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B + 6 * t)
    (B : SecondSubconstituent G x) :
    5 * (a ᵥ* localAdjacencyMatrix G x) B = 12 * t - 60 * a B := by
  have hprofile :
      a ᵥ* localGramMatrix G x = fun C => 45 * a C + 6 * t := by
    funext C
    simpa [Matrix.vecMul_apply_eq_sum] using haffine C
  have hinter := affineLocalGramProfile_mul_intersection G hG x a t
    hsum haffine B
  have hdecomp := congrArg (Matrix.vecMul a)
    (localGramMatrix_eq_linear_combination G x)
  have hdecompB := congrFun hdecomp B
  rw [hprofile] at hdecompB
  simp only [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Nat.smul_one_eq_cast] at hdecompB
  simp only [Matrix.vecMul_natCast, Pi.smul_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    nsmul_eq_mul] at hdecompB
  norm_num at hdecompB
  have hones :
      (a ᵥ* (allOnesMatrix :
        Matrix (SecondSubconstituent G x)
          (SecondSubconstituent G x) ℤ)) B = 11 * t := by
    simpa [Matrix.vecMul_apply_eq_sum, allOnesMatrix_apply] using hsum
  rw [hones] at hdecompB
  linarith

/-- A zero-centroid affine profile is a signed trade in the local
`2-(45,9,8)` design: every point occurs equally often with positive and
negative sign. -/
theorem affineLocalGramProfile_mul_incidence_of_centroid_zero
    (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ)
    (hsum : ∑ B, a B = 0)
    (haffine : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B) :
    localIncidenceMatrix G x *ᵥ a = 0 := by
  have haffine' : ∀ B : SecondSubconstituent G x,
      (∑ C, a C * localGramMatrix G x C B) = 45 * a B + 6 * 0 := by
    simpa using haffine
  have hinter (B : SecondSubconstituent G x) :
      (a ᵥ* localIntersectionMatrix G x) B = 0 := by
    have h := affineLocalGramProfile_mul_intersection
      G hG x a 0 (by simpa using hsum) haffine' B
    omega
  have hSmul : localIntersectionMatrix G x *ᵥ a = 0 := by
    funext B
    rw [Matrix.mulVec_apply_eq_sum]
    change ∑ C, localIntersectionMatrix G x B C * a C = 0
    calc
      ∑ C, localIntersectionMatrix G x B C * a C =
          ∑ C, a C * localIntersectionMatrix G x C B := by
        apply Finset.sum_congr rfl
        intro C _
        rw [localIntersectionMatrix_comm G x B C]
        ring
      _ = (a ᵥ* localIntersectionMatrix G x) B := by
        rw [Matrix.vecMul_apply_eq_sum]
      _ = 0 := hinter B
  let r : FirstSubconstituent G x → ℤ :=
    localIncidenceMatrix G x *ᵥ a
  have hnorm : r ⬝ᵥ r = 0 := by
    calc
      r ⬝ᵥ r =
          a ⬝ᵥ (localIncidenceMatrix G x)ᵀ *ᵥ r := by
        symm
        exact Matrix.dotProduct_transpose_mulVec
          (localIncidenceMatrix G x) a r
      _ = a ⬝ᵥ ((localIncidenceMatrix G x)ᵀ *
          localIncidenceMatrix G x) *ᵥ a := by
        rw [Matrix.mulVec_mulVec]
      _ = a ⬝ᵥ localIntersectionMatrix G x *ᵥ a := by
        rfl
      _ = 0 := by rw [hSmul]; simp
  funext p
  have hnonneg : ∀ q ∈ (Finset.univ : Finset (FirstSubconstituent G x)),
      0 ≤ r q * r q := by
    intro q _
    exact mul_self_nonneg _
  have hsingle : r p * r p ≤ ∑ q, r q * r q :=
    Finset.single_le_sum hnonneg (Finset.mem_univ p)
  change r p = 0
  simp only [dotProduct] at hnorm
  rw [hnorm] at hsingle
  nlinarith

/-- Every norm-one direction has centroid coordinate divisible by five.
This uses the local incidence design, not any rank-15 host classification. -/
theorem Rank15EmbeddingWitness.five_dvd_centroidCoordinate
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier) :
    (5 : ℤ) ∣ E.centroidCoordinate (G := G) c u := by
  have h := affineLocalGramProfile_mul_intersection G hG x
    (E.directionProfile (G := G) u)
    (E.centroidCoordinate (G := G) c u)
    (E.directionProfile_sum (G := G) c hc u)
    (E.directionProfile_mul_localGram (G := G) hG c hc u)
  obtain ⟨D⟩ : Nonempty (SecondSubconstituent G x) := by
    exact Fintype.card_pos_iff.mp (by
      rw [secondSubconstituent_card G hG x]
      norm_num)
  have hD := h D
  omega

/-- Together with the projector bound, the divisibility collapses the
centroid coordinate of a norm-one direction to three values. -/
theorem Rank15EmbeddingWitness.centroidCoordinate_cases_sharp
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    E.centroidCoordinate (G := G) c u = -5 ∨
      E.centroidCoordinate (G := G) c u = 0 ∨
        E.centroidCoordinate (G := G) c u = 5 := by
  have hdiv := E.five_dvd_centroidCoordinate (G := G) hG c hc u
  have hbound := E.centroidCoordinate_abs_le_five (G := G) hG c hc u hu
  rcases hdiv with ⟨k, hk⟩
  have hbounds :
      -5 ≤ E.centroidCoordinate (G := G) c u ∧
        E.centroidCoordinate (G := G) c u ≤ 5 := by
    exact abs_le.mp hbound
  omega

/-- Exact finite audit object produced by any norm-one host direction.  The
remaining mixed-component problem may consume this structure without knowing
anything about quotient lattices or the Yang--Yoshino embedding construction. -/
structure NormOneDirectionAuditProfile
    (x : V) (E : Rank15EmbeddingWitness G x) (u : E.host.carrier) where
  centroid : IntegralGramLattice G x
  centroid_eq :
    (11 : ℤ) • centroid = integralGramGeneratorSum G x
  entry_cases : ∀ B : SecondSubconstituent G x,
    E.directionProfile (G := G) u B = -1 ∨
      E.directionProfile (G := G) u B = 0 ∨
        E.directionProfile (G := G) u B = 1
  signed_sum :
    (∑ B, E.directionProfile (G := G) u B) =
      11 * E.centroidCoordinate (G := G) centroid u
  affine_eigenvector : ∀ B : SecondSubconstituent G x,
    (∑ C, E.directionProfile (G := G) u C *
        localGramMatrix G x C B) =
      45 * E.directionProfile (G := G) u B +
        6 * E.centroidCoordinate (G := G) centroid u
  square_sum_lower :
    11 * |E.centroidCoordinate (G := G) centroid u| ≤
      E.directionSquareSum (G := G) u
  square_sum_upper :
    5 * E.directionSquareSum (G := G) u ≤
      225 + 2 * E.centroidCoordinate (G := G) centroid u ^ 2
  centroid_bound :
    |E.centroidCoordinate (G := G) centroid u| ≤ 5

/-- Construction of the complete bounded audit profile is native Lean. -/
theorem Rank15EmbeddingWitness.exists_normOneDirectionAuditProfile
    (E : Rank15EmbeddingWitness G x)
    (hG : IsHypothetical G)
    (u : E.host.carrier)
    (hu : E.host.pairing u u = 1) :
    Nonempty (NormOneDirectionAuditProfile G x E u) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  exact ⟨{
    centroid := c
    centroid_eq := hc
    entry_cases := E.directionProfile_cases (G := G) hG u hu
    signed_sum := E.directionProfile_sum (G := G) c hc u
    affine_eigenvector :=
      E.directionProfile_mul_localGram (G := G) hG c hc u
    square_sum_lower :=
      E.directionProfile_lower_bound (G := G) hG c hc u hu
    square_sum_upper :=
      E.directionProfile_upper_bound (G := G) hG c hc u hu
    centroid_bound :=
      E.centroidCoordinate_abs_le_five (G := G) hG c hc u hu }⟩

/-- The exact pure-core condition on an embedded local lattice: every
norm-one host direction is orthogonal to all distinguished generators. -/
def Rank15EmbeddingWitness.NormOneDirectionsOrthogonal
    (E : Rank15EmbeddingWitness G x) : Prop :=
  ∀ u : E.host.carrier, E.host.pairing u u = 1 →
    ∀ B : SecondSubconstituent G x,
      E.directionProfile (G := G) u B = 0

end SRG266
