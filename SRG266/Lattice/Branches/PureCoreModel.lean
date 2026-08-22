/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HostBuilder
import SRG266.NormOneDirections

/-!
# Coordinate models of the norm-one-free core

A rank-15 host `L` splits as `ℤ^k ⊥ L₀` with `L₀` free of norm-one vectors,
and the *pure* case of the
trichotomy is the one where every embedded local Gram generator — and hence the
embedded centroid — lies in `L₀`.  Each pure branch then argues inside a
coordinate model of `L₀`.

This file is the plumbing every pure branch shares.

* `SRG266.Lattice.IsHostCoreModel` states that the vectors orthogonal to a
  chosen orthonormal family are covered by an isometric image of the coordinate
  lattice of an integer Gram matrix.  No submodule appears, so the
  `ModuleCat ℤ` instance diamond
  described in `SRG266/Lattice/Core.lean` is never touched.
* `SRG266.Lattice.PureCoreModel` bundles the data a branch actually reads: a
  pairing-preserving map from `Fin n → ℤ`, coefficient vectors for the `220`
  generators, and a coefficient vector for the centroid.
* `SRG266.Lattice.PureCoreModel.exists_of_isHostCoreModel` builds it from
  purity, using only that `11 • c` is the generator sum.
* `SRG266.Lattice.PureCoreModel.coords_injective` and
  `SRG266.Lattice.PureCoreModel.generator_sum` read `∑_B v_B = 11 c` inside the
  model; injectivity of the presentation is free from positive definiteness of
  `A`, so it is not a field of the structure.

Nothing here is host-specific.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **A coordinate model of the norm-one-free core.**  Every host vector
orthogonal to all of `u` lies in the image of a pairing-preserving map from the
coordinate lattice of `A`.

Injectivity of the map is not demanded: it follows from positive definiteness of
`A` and is never used. -/
def IsHostCoreModel (L : OddUnimodularLattice15) {k : ℕ} (u : Fin k → L.carrier)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ f : (Fin n → ℤ) →ₗ[ℤ] L.carrier,
    (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w) ∧
    ∀ y : L.carrier, (∀ i, L.pairing (u i) y = 0) → ∃ v, f v = y

variable {G}

/-- **The pure-branch working data.**  A pairing-preserving presentation of the
core by the coordinate lattice of `A`, together with the coefficient vectors of
the `220` embedded generators and of the embedded centroid. -/
structure PureCoreModel {x : V} (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) where
  /-- The coordinate presentation of the core. -/
  coords : (Fin n → ℤ) →ₗ[ℤ] E.host.carrier
  /-- The presentation transports the Gram form of `A`. -/
  pairing_coords : ∀ v w, E.host.pairing (coords v) (coords w) = Matrix.toBilin' A v w
  /-- Coefficient vector of an embedded generator. -/
  generator : SecondSubconstituent G x → Fin n → ℤ
  /-- The coefficient vector really presents the generator. -/
  coords_generator : ∀ B, coords (generator B) = E.embeddedGenerator (G := G) B
  /-- Coefficient vector of the embedded centroid. -/
  centroid : Fin n → ℤ
  /-- The coefficient vector really presents the centroid. -/
  coords_centroid : coords centroid = E.embeddedCentroid (G := G) c

namespace PureCoreModel

variable {x : V} {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}

/-- **The coordinate presentation is injective.**  Positive definiteness of `A`
is all it takes, so the `PureCoreModel` structure does not carry injectivity as
a field. -/
theorem coords_injective (M : PureCoreModel E c A)
    (hpd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v) :
    Function.Injective M.coords := by
  intro v w hvw
  by_contra hne
  have hsub : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hzero : M.coords (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hform := M.pairing_coords (v - w) (v - w)
  rw [hzero] at hform
  simp only [map_zero] at hform
  exact (hpd _ hsub).ne' hform.symm

/-- The Gram matrix of the coefficient vectors of two generators is the local
Gram matrix. -/
theorem gram (M : PureCoreModel E c A) (B C : SecondSubconstituent G x) :
    Matrix.toBilin' A (M.generator B) (M.generator C) = localGramMatrix G x B C := by
  rw [← M.pairing_coords, M.coords_generator, M.coords_generator,
    E.embeddedGenerator_pairing (G := G)]

/-- Every generator has norm three. -/
theorem generator_norm (M : PureCoreModel E c A) (hG : IsHypothetical G)
    (B : SecondSubconstituent G x) :
    Matrix.toBilin' A (M.generator B) (M.generator B) = 3 := by
  rw [M.gram B B, localGramMatrix_diagonal G hG x B]

/-- The centroid has norm three hundred. -/
theorem centroid_norm (M : PureCoreModel E c A) (hG : IsHypothetical G)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Matrix.toBilin' A M.centroid M.centroid = 300 := by
  rw [← M.pairing_coords, M.coords_centroid, E.embeddedCentroid_norm (G := G) hG c hc]

/-- The centroid pairs to fifteen with every generator. -/
theorem centroid_generator (M : PureCoreModel E c A) (hG : IsHypothetical G)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (B : SecondSubconstituent G x) :
    Matrix.toBilin' A M.centroid (M.generator B) = 15 := by
  rw [← M.pairing_coords, M.coords_centroid, M.coords_generator,
    E.embeddedCentroid_pairing_generator (G := G) hG c hc]

/-- **The generators sum to eleven times the centroid**, read in coordinates.
This is `11 • c = ∑ v_B` transported through the presentation; it needs
injectivity, hence positive definiteness of `A`. -/
theorem generator_sum (M : PureCoreModel E c A)
    (hpd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∑ B, M.generator B = (11 : ℤ) • M.centroid := by
  refine M.coords_injective hpd ?_
  have hleft : M.coords (∑ B, M.generator B) = E.embedding ((11 : ℤ) • c) := by
    rw [map_sum, Finset.sum_congr rfl fun B _ => M.coords_generator B,
      E.sum_embeddedGenerator (G := G) c hc]
  have hright : M.coords ((11 : ℤ) • M.centroid) = E.embedding ((11 : ℤ) • c) := by
    rw [LinearMap.map_smul, M.coords_centroid, LinearMap.map_smul]
    rfl
  rw [hleft, hright]

/-- The direction profile of a coordinate vector, read inside the model. -/
theorem directionProfile_coords (M : PureCoreModel E c A) (v : Fin n → ℤ)
    (B : SecondSubconstituent G x) :
    E.directionProfile (G := G) (M.coords v) B = Matrix.toBilin' A v (M.generator B) := by
  rw [Rank15EmbeddingWitness.directionProfile, ← M.coords_generator B, M.pairing_coords]

/-- The centroid coordinate of a coordinate vector, read inside the model. -/
theorem centroidCoordinate_coords (M : PureCoreModel E c A) (v : Fin n → ℤ) :
    E.centroidCoordinate (G := G) c (M.coords v) = Matrix.toBilin' A v M.centroid := by
  rw [Rank15EmbeddingWitness.centroidCoordinate, ← M.coords_centroid, M.pairing_coords]

/-- **Every coefficient of the centroid is divisible by five in a unimodular
coordinate model.**

`Rank15EmbeddingWitness.five_dvd_centroidCoordinate` says that pairing the
centroid with *any* integral host vector is divisible by five.  If `A` has an
integer inverse, its inverse columns are the dual basis vectors, so these pairings
recover the individual coefficients of `M.centroid`.

This is the coordinate-free congruence behind the divisibility pattern in the
`E7` and `A15` centroid sweeps. -/
theorem centroid_coeff_five_dvd (M : PureCoreModel E c A)
    (hG : IsHypothetical G)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (Ainv : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm)
    (hinv : A * Ainv = 1)
    (i : Fin n) :
    (5 : ℤ) ∣ M.centroid i := by
  let v : Fin n → ℤ := fun j => Ainv j i
  have hdiv := E.five_dvd_centroidCoordinate
    (G := G) hG c hc (M.coords v)
  rw [M.centroidCoordinate_coords v] at hdiv
  have hcoeff : Matrix.toBilin' A v M.centroid = M.centroid i := by
    rw [Matrix.toBilin'_apply]
    calc
      (∑ j, ∑ k, v j * A j k * M.centroid k) =
          ∑ k, (A * Ainv) k i * M.centroid k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by
          rw [hsym.apply k j]
          simp only [v]
          ring
      _ = ∑ k, (1 : Matrix (Fin n) (Fin n) ℤ) k i * M.centroid k := by
        rw [hinv]
      _ = M.centroid i := by
        simp [Matrix.one_apply]
  rwa [hcoeff] at hdiv

/-- Every integral linear coordinate read from the centroid is divisible by
five.  This is the form used by the concrete `A15` and `E7 ⊕ E7` host
coordinates. -/
theorem centroid_vecMul_five_dvd (M : PureCoreModel E c A)
    (hG : IsHypothetical G)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (Ainv : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm)
    (hinv : A * Ainv = 1)
    {ι : Type*} [Fintype ι]
    (C : Matrix (Fin n) ι ℤ) (j : ι) :
    (5 : ℤ) ∣ Matrix.vecMul M.centroid C j := by
  rw [Matrix.vecMul_apply_eq_sum]
  exact Finset.dvd_sum fun i _ =>
    dvd_mul_of_dvd_left (M.centroid_coeff_five_dvd hG hc Ainv hsym hinv i) (C i j)

/-- The host norm of a coordinate vector, read inside the model. -/
theorem host_norm_coords (M : PureCoreModel E c A) (v : Fin n → ℤ) :
    E.host.pairing (M.coords v) (M.coords v) = Matrix.toBilin' A v v :=
  M.pairing_coords v v

/-- The squared profile size of a coordinate vector, read inside the model. -/
theorem directionSquareSum_coords (M : PureCoreModel E c A) (v : Fin n → ℤ) :
    E.directionSquareSum (G := G) (M.coords v) =
      ∑ B, Matrix.toBilin' A v (M.generator B) ^ 2 :=
  Finset.sum_congr rfl fun B _ => by rw [M.directionProfile_coords v B]

/-- The projector bound inside the model, applied at coordinate vectors of norm
larger than one. -/
theorem projector_bound (M : PureCoreModel E c A) (hG : IsHypothetical G)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (v : Fin n → ℤ) :
    5 * ∑ B, Matrix.toBilin' A v (M.generator B) ^ 2 ≤
      225 * Matrix.toBilin' A v v + 2 * Matrix.toBilin' A v M.centroid ^ 2 := by
  have h := E.directionSquareSum_le' (G := G) hG c hc (M.coords v)
  rwa [M.directionSquareSum_coords v, M.host_norm_coords v,
    M.centroidCoordinate_coords v] at h

end PureCoreModel

end Lattice
end SRG266
