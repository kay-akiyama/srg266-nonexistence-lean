/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.A15MinedCentroidReindex
import SRG266.Lattice.Branches.A15MinedShellFacts

/-! # Combined raw payload for the mined A15 construction -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Canonically reindexed centroid data together with generator shell facts. -/
structure A15MinedRawPayload (x : V) extends A15MinedShellFacts (G := G) x where
  coordinates : List ℤ
  permutation : Equiv.Perm (Fin 16)
  profile : coordinates ∈ a15MinedNormProfiles
  scaled_profile :
    a15SmallProfile coordinates = fun i => centroid (permutation i)

/-- Combine the independently elaborated centroid and generator packages. -/
theorem a15MinedRawPayload_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    Nonempty (A15MinedRawPayload (G := G) x) := by
  obtain ⟨S, hScentroid⟩ := a15MinedShellFacts_of_pureCoreModel hG hc M
  obtain ⟨coordinates, τ, hprofile, hscaled⟩ :=
    a15MinedCentroidReindex_of_pureCoreModel hG hc M
  have hscaled' :
      a15SmallProfile coordinates = fun i => S.centroid (τ i) := by
    rw [hScentroid]
    exact hscaled
  exact ⟨{
    toA15MinedShellFacts := S
    coordinates := coordinates
    permutation := τ
    profile := hprofile
    scaled_profile := hscaled'
  }⟩

end Lattice
end SRG266
