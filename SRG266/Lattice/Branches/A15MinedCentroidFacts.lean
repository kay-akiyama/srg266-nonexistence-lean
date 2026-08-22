/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.A15MinedCentroid

/-! # Bounded centroid facts for the mined A15 construction -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The divided centroid has squared norm 48, bounded coordinates, and one of
the 17 canonical mined profiles. -/
theorem a15MinedCentroidFacts_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    ∃ z : Fin 16 → ℤ,
      (∀ i, Matrix.vecMul M.centroid a15PlusCoords i = 10 * z i) ∧
      (∀ i, -6 ≤ z i ∧ z i ≤ 6) ∧
      a15SmallCanonicalCoordinates (List.ofFn z) ∈ a15MinedNormProfiles := by
  obtain ⟨z, hz, hzMined⟩ :=
    a15Plus_centroid_minedNormProfile hG hc M
  have hsq := sum_sq_vecMul_coords a15PlusGram a15PlusCoords 4
    a15PlusCoords_gram M.centroid
  rw [M.centroid_norm hG hc,
    Finset.sum_congr rfl fun i _ => by rw [hz i]] at hsq
  have hzsq : ∑ i, z i ^ 2 = 48 := by
    have hexp : ∑ i, (10 * z i) ^ 2 = 100 * ∑ i, z i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp] at hsq
    omega
  have hzbound : ∀ i, -6 ≤ z i ∧ z i ≤ 6 := by
    intro i
    have hle : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
      Finset.single_le_sum (f := fun j => z j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hzsq] at hle
    constructor <;> nlinarith
  exact ⟨z, hz, hzbound, hzMined⟩

end Lattice
end SRG266
