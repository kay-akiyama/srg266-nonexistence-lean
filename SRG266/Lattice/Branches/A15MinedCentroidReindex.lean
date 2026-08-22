/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.A15MinedCentroidFacts
import SRG266.Lattice.Branches.A15Shell

/-! # Canonical reindexing for the mined A15 centroid -/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Canonically reorder the divided centroid and realize the value-list
permutation on `Fin 16`. -/
theorem a15MinedCentroidReindex_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    ∃ (coordinates : List ℤ) (τ : Equiv.Perm (Fin 16)),
      coordinates ∈ a15MinedNormProfiles ∧
      a15SmallProfile coordinates =
        fun i => Matrix.vecMul M.centroid a15PlusCoords (τ i) := by
  classical
  obtain ⟨z, hz, hzbound, hzMined⟩ :=
    a15MinedCentroidFacts_of_pureCoreModel hG hc M
  let coordinates := a15SmallCanonicalCoordinates (List.ofFn z)
  have hperm : coordinates.Perm (List.ofFn z) :=
    a15SmallCanonicalCoordinates_perm _
      (List.forall_mem_ofFn_iff.mpr hzbound)
  have hlen : coordinates.length = 16 :=
    hperm.length_eq.trans (by simp)
  have hofFn :
      List.ofFn (fun i : Fin 16 => coordinates.getD i.1 0) = coordinates := by
    refine List.ext_getElem (by rw [List.length_ofFn, hlen]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn]
    simp [List.getD, h2]
  obtain ⟨τ, hτ⟩ :=
    exists_perm_comp_of_ofFn_perm
      (f := fun i : Fin 16 => coordinates.getD i.1 0) (g := z)
      (by rw [hofFn]; exact hperm)
  refine ⟨coordinates, τ, hzMined, ?_⟩
  funext i
  change 10 * coordinates.getD i.1 0 =
    Matrix.vecMul M.centroid a15PlusCoords (τ i)
  rw [← hτ i]
  exact (hz (τ i)).symm

end Lattice
end SRG266
