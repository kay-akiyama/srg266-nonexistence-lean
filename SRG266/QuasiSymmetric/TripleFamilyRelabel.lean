/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesignSymmetry
import SRG266.QuasiSymmetric.TripleCodes

/-!
# Relabelling packed triple families

Finite normal-form certificates store first neighbourhoods as 2048-bit family
masks.  This module defines the action of a vertex permutation on those masks
without a trusted lookup table and proves that it agrees with the mathematical
`GlobalDesign.relabel` action.
-/

namespace SRG266.QuasiSymmetric

/-- Decode the triple positions selected by a packed family mask. -/
def tripleFamilyOfMask (familyMask : ℕ) : Finset (Finset (Fin 11)) :=
  triples.filter fun U => familyMask.testBit (vertexMask U)

/-- Decoding the mask of a family containing only triples recovers the family. -/
theorem tripleFamilyOfMask_vertexFamilyMask
    {S : Finset (Finset (Fin 11))} (hclosed : ∀ U ∈ S, U ∈ triples) :
    tripleFamilyOfMask (vertexFamilyMask S) = S := by
  ext U
  simp only [tripleFamilyOfMask, Finset.mem_filter]
  rw [testBit_vertexFamilyMask_vertexMask]
  constructor
  · rintro ⟨_, hU⟩
    simpa using hU
  · intro hU
    exact ⟨hclosed U hU, decide_eq_true hU⟩

/-- Relabel a packed triple family by a permutation of the eleven vertices. -/
def relabelTripleFamilyMask (σ : Equiv.Perm (Fin 11))
    (familyMask : ℕ) : ℕ :=
  vertexFamilyMask ((tripleFamilyOfMask familyMask).image fun U => U.image σ)

/-- On a mathematical triple family, packed relabelling is exactly image under
the vertex permutation. -/
theorem relabelTripleFamilyMask_vertexFamilyMask
    (σ : Equiv.Perm (Fin 11)) {S : Finset (Finset (Fin 11))}
    (hclosed : ∀ U ∈ S, U ∈ triples) :
    relabelTripleFamilyMask σ (vertexFamilyMask S) =
      vertexFamilyMask (S.image fun U => U.image σ) := by
  rw [relabelTripleFamilyMask, tripleFamilyOfMask_vertexFamilyMask hclosed]

namespace GlobalDesign

variable (G : GlobalDesign)

/-- The packed first-neighbourhood mask of a relabelled global design is the
packed relabelling of the original mask whenever the named root is fixed. -/
theorem vertexFamilyMask_disjointFrom_relabel_of_fixed
    (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11))
    (hfix : T.image σ = T) :
    vertexFamilyMask ((G.relabel σ).disjointFrom T) =
      relabelTripleFamilyMask σ (vertexFamilyMask (G.disjointFrom T)) := by
  rw [G.disjointFrom_relabel, image_symm_eq_self hfix]
  symm
  apply relabelTripleFamilyMask_vertexFamilyMask
  intro U hU
  exact (G.mem_disjointFrom.mp hU).1

end GlobalDesign

end SRG266.QuasiSymmetric
