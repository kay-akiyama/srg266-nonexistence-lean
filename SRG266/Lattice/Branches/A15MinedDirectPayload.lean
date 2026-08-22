/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.A15MinedRawPayload
import SRG266.Lattice.Branches.A15Shell

/-! # Direct shell realization for the mined A15 payload -/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The minimal payload consumed by the mined A15 transport. -/
structure A15MinedDirectPayload (x : V) where
  coordinates : List ℤ
  profile : coordinates ∈ a15MinedNormProfiles
  realization : A15ShellGramRealization G x (a15SmallProfile coordinates)

/-- Feed the reindexed integer identities to the shell-realization builder. -/
theorem A15MinedRawPayload.toDirectPayload {x : V}
    (D : A15MinedRawPayload (G := G) x) :
    Nonempty (A15MinedDirectPayload (G := G) x) := by
  classical
  have hshell : ∀ B,
      (∀ i, D.generator B i = a15RawVector (D.support B) i) ∨
        (∀ i, D.generator B i = -a15RawVector (D.support B) i) := by
    intro B
    rcases D.shell B with h | h
    · exact Or.inl h
    · refine Or.inr fun i => ?_
      rw [h i, a15RawVector]
      by_cases hi : i ∈ D.support B <;> simp [hi]
  refine ⟨{
    coordinates := D.coordinates
    profile := D.profile
    realization := ?_
  }⟩
  rw [D.scaled_profile]
  let τ := D.permutation
  refine Nonempty.some (a15ShellGramRealization_of_data (G := G) (x := x)
    (fun i => D.centroid (τ i))
    ((Equiv.sum_comp τ D.centroid).trans D.centroid_sum)
    (fun B i => D.generator B (τ i))
    (fun B => (D.support B).map τ.symm.toEmbedding)
    (fun B => by rw [Finset.card_map]; exact D.support_card B)
    (fun B => by
      rcases hshell B with h | h
      · exact Or.inl fun i => by rw [a15RawVector_map]; exact h (τ i)
      · exact Or.inr fun i => by rw [a15RawVector_map]; exact h (τ i))
    (fun B =>
      (Equiv.sum_comp τ (fun i => D.centroid i * D.generator B i)).trans
        (D.centroid_pair B))
    (fun B C =>
      (Equiv.sum_comp τ
        (fun i => D.generator B i * D.generator C i)).trans (D.gram B C))
    (fun i => D.generator_sum (τ i)))

/-- A pure A15 core produces the minimal mined payload. -/
theorem a15MinedDirectPayload_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    Nonempty (A15MinedDirectPayload (G := G) x) := by
  obtain ⟨raw⟩ := a15MinedRawPayload_of_pureCoreModel hG hc M
  exact raw.toDirectPayload

end Lattice
end SRG266
