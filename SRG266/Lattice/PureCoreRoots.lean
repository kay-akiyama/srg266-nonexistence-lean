/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCore
import SRG266.ProjectorClasses

/-!
# A norm-two vector in every pure graph core

The rooted host-classification statement asks for a norm-two vector in the
frame complement.  A hypothetical graph supplies one without any lattice
classification: two local Gram generators with mutual entry two differ by a
vector of norm two.

These lemmas are isolated from `SRG266.Lattice.KneserBoundary` so the direct
mined branch dispatcher can use them without importing the aggregate audited-host
interface or either whole-search certificate assembly.
-/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every local Gram generator has an inner-product-two neighbour. -/
theorem exists_localGramMatrix_eq_two (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∃ D : SecondSubconstituent G x, localGramMatrix G x B D = 2 := by
  classical
  have hcard := gramEntryTwo_card_add_three_mul_class_card G hG x B
  have hle := gramClass_card_le_three G hG x B
  have hne : (gramEntryIndices G x B 2).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨D, hD⟩ := hne
  exact ⟨D, (mem_gramEntryIndices G x B D 2).mp hD⟩

/-- The difference of two embedded generators with local Gram entry two is a
norm-two vector orthogonal to every chosen norm-one frame direction. -/
theorem exists_pureCore_norm_two {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier}
    (hu : ∀ i, E.host.pairing (u i) (u i) = 1) :
    ∃ a : E.host.carrier,
      (∀ i, E.host.pairing (u i) a = 0) ∧ E.host.pairing a a = 2 := by
  classical
  have hnonempty : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by
      rw [secondSubconstituent_card G hG x]
      omega)
  obtain ⟨B⟩ := hnonempty
  obtain ⟨D, hD⟩ := exists_localGramMatrix_eq_two G hG x B
  refine ⟨E.embeddedGenerator (G := G) B -
      E.embeddedGenerator (G := G) D, ?_, ?_⟩
  · intro i
    have hB : E.host.pairing (u i) (E.embeddedGenerator (G := G) B) = 0 :=
      hpure (u i) (hu i) B
    have hD' : E.host.pairing (u i) (E.embeddedGenerator (G := G) D) = 0 :=
      hpure (u i) (hu i) D
    rw [map_sub, hB, hD', sub_zero]
  · have hBB := E.embeddedGenerator_pairing (G := G) B B
    have hBD := E.embeddedGenerator_pairing (G := G) B D
    have hDD := E.embeddedGenerator_pairing (G := G) D D
    have hDB : E.host.pairing (E.embeddedGenerator (G := G) D)
        (E.embeddedGenerator (G := G) B) = 2 := by
      rw [E.host.symmetric.eq, hBD, hD]
    rw [localGramMatrix_diagonal G hG x B] at hBB
    rw [localGramMatrix_diagonal G hG x D] at hDD
    rw [hD] at hBD
    simp only [map_sub, LinearMap.sub_apply, hBB, hBD, hDB, hDD]
    ring

end Lattice
end SRG266
