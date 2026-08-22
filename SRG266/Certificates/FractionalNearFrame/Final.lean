/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.FractionalNearFrame.All
import SRG266.QuasiSymmetric.FractionalNearFrameCoordinates
import SRG266.QuasiSymmetric.RootedSearchNormalization

/-!
# The fractional near-frame obstruction

This module closes the residual cherry-cover boundary.  A hypothetical global
design is rooted at a non-`2K4` block, moved to `{0,1,2}`, and then moved within
the stabilizer of that root to one of the 2,752 checked near normal forms.  The
nine group-zero forms reconstruct the excluded `2K4` root.  Every other form
is refuted by a theorem-mined Hall cut, a bounded kernel separator proof, or
an exact integer Farkas vector.

The mathematical transport from a global design to the compact rational
system is proved in ordinary Lean.  Every payload-free stratum is derived from
the Hall theorem in the kernel; generated separator data remains only on the
residual Farkas branches imported by `All`.
-/

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The compact root graph reconstructed by each of the nine exceptional
near normal forms. -/
def twoK4CompactRootGraph : ℕ := 264249735

private theorem group0_rootGraph_audit :
    rootNearRepresentativeGroup0.all (fun nearMask =>
      decide (reconstructedRootGraph8 nearMask = twoK4CompactRootGraph)) =
        true := by
  decide +kernel

theorem reconstructedRootGraph8_eq_twoK4_of_mem_group0
    {nearMask : ℕ} (hmem : nearMask ∈ rootNearRepresentativeGroup0) :
    reconstructedRootGraph8 nearMask = twoK4CompactRootGraph := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp group0_rootGraph_audit) nearMask hmem)

theorem mem_rootNearRepresentatives_group0_or_nonTwoK4
    {nearMask : ℕ} (hmem : nearMask ∈ rootNearRepresentatives) :
    nearMask ∈ rootNearRepresentativeGroup0 ∨
      nearMask ∈ rootNearRepresentativesNonTwoK4 := by
  simpa [rootNearRepresentatives, rootNearRepresentativeGroups,
    rootNearRepresentativesNonTwoK4, List.mem_append] using hmem

end SRG266.Certificates

namespace SRG266.QuasiSymmetric

open SRG266.Certificates

/-- The exceptional compact root graph is the union of the cliques on
`{3,4,5,6}` and `{7,8,9,10}`. -/
theorem isTwoK4_fixedRoot_twoK4CompactRootGraph :
    IsTwoK4 fixedRoot012 (rootEdgeFamily8 twoK4CompactRootGraph) := by
  refine ⟨?_, (fun vertex => decide (vertex.val < 7)), ?_, ?_⟩
  · decide +kernel
  · intro bit
    cases bit <;> decide +kernel
  · intro v w hvw
    revert v w
    decide +kernel

/-- The complete normal-form and Farkas audit rules out the global design
extracted from any residual cherry cover. -/
theorem isEmpty_globalDesign_of_fractionalNearFrameAudit :
    RootNearNormalFormCover rootNearRepresentatives → IsEmpty GlobalDesign := by
  intro hnormalForms
  refine ⟨fun G => ?_⟩
  obtain ⟨T, hT, hnotT⟩ := G.exists_nonTwoK4_root
  have hcard : T.card = fixedRoot012.card := by
    exact (mem_triples.mp hT).trans
      (mem_triples.mp fixedRoot012_mem_triples).symm
  obtain ⟨initialPermutation, hinitial⟩ := exists_perm_image_eq hcard
  let G₁ := G.relabel initialPermutation
  have hpreimage : fixedRoot012.image initialPermutation.symm = T := by
    rw [← hinitial, image_perm_image_symm]
  have hblock₁ : G₁.block fixedRoot012 =
      (G.block T).image (Edge11.map initialPermutation) := by
    change (G.relabel initialPermutation).block fixedRoot012 = _
    rw [G.block_relabel, hpreimage]
  have hnot₁ : ¬ IsTwoK4 fixedRoot012 (G₁.block fixedRoot012) := by
    intro hTwo
    have hTwoImage : IsTwoK4 (T.image initialPermutation)
        ((G.block T).image (Edge11.map initialPermutation)) := by
      rw [hinitial, ← hblock₁]
      exact hTwo
    exact hnotT ((isTwoK4_image_iff initialPermutation).mp hTwoImage)
  let R₁ : GlobalDesignRoot :=
    G₁.toGlobalDesignRoot fixedRoot012 fixedRoot012_mem_triples
  have hrootMask₁ : vertexMask R₁.root = 7 := by
    change vertexMask fixedRoot012 = 7
    exact vertexMask_fixedRoot012
  have hnearDomain :
      vertexFamilyMask R₁.near ∈ rootNearFreeDomain 7 := by
    rw [← hrootMask₁]
    exact R₁.actualNearMask_mem_rootNearFreeDomain
  obtain ⟨normalPermutation, hfix, nearMask, hrepresentative, hnormal⟩ :=
    hnormalForms (vertexFamilyMask R₁.near) hnearDomain
  let G₂ := G₁.relabel normalPermutation
  have hblock₂ : G₂.block fixedRoot012 =
      (G₁.block fixedRoot012).image (Edge11.map normalPermutation) := by
    change (G₁.relabel normalPermutation).block fixedRoot012 = _
    exact G₁.block_relabel_of_image_eq hfix
  have hnot₂ : ¬ IsTwoK4 fixedRoot012 (G₂.block fixedRoot012) := by
    intro hTwo
    have hTwoImage : IsTwoK4 (fixedRoot012.image normalPermutation)
        ((G₁.block fixedRoot012).image (Edge11.map normalPermutation)) := by
      rw [hfix, ← hblock₂]
      exact hTwo
    exact hnot₁ ((isTwoK4_image_iff normalPermutation).mp hTwoImage)
  have hnear₂ : vertexFamilyMask (G₂.disjointFrom fixedRoot012) =
      expandRootNearMask nearMask := by
    calc
      vertexFamilyMask (G₂.disjointFrom fixedRoot012) =
          relabelTripleFamilyMask normalPermutation
            (vertexFamilyMask (G₁.disjointFrom fixedRoot012)) := by
        change vertexFamilyMask
            ((G₁.relabel normalPermutation).disjointFrom fixedRoot012) = _
        exact G₁.vertexFamilyMask_disjointFrom_relabel_of_fixed
          normalPermutation fixedRoot012 hfix
      _ = expandRootNearMask nearMask := hnormal
  let R : RegularNonTwoK4RootedCubicLift :=
    G₂.toRegularNonTwoK4RootedCubicLiftAt fixedRoot012
      fixedRoot012_mem_triples hnot₂
  have hroot : R.root = fixedRoot012 := rfl
  have hnear : vertexFamilyMask R.near = expandRootNearMask nearMask := by
    change vertexFamilyMask (G₂.disjointFrom fixedRoot012) = _
    exact hnear₂
  rcases mem_rootNearRepresentatives_group0_or_nonTwoK4 hrepresentative with
    hgroup0 | hnonTwoK4
  · apply R.root_not_twoK4
    have hrootGraph :=
      reconstructedRootGraph8_eq_twoK4_of_mem_group0 hgroup0
    rw [R.rootBlock_eq_rootEdgeFamily8 hroot hnear, hroot, hrootGraph]
    exact isTwoK4_fixedRoot_twoK4CompactRootGraph
  · exact (noCompactFractionalNearFrame_of_mem_nonTwoK4 hnonTwoK4)
      (R.compactFractionalNearFrameOf R.toFractionalNearFrame hroot hnear)

/-- The residual cherry-cover obstruction follows from the finite audit. -/
theorem noResidualCherryCover_of_fractionalNearFrameAudit
    (hnormalForms : RootNearNormalFormCover rootNearRepresentatives) :
    NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_fractionalNearFrameAudit hnormalForms)

/-- In particular, the corresponding quasi-symmetric design cannot exist. -/
theorem noQuasiSymmetricDesign56_fractionalNearFrame :
    RootNearNormalFormCover rootNearRepresentatives →
      NoQuasiSymmetricDesign56.{u} := fun hnormalForms =>
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_fractionalNearFrameAudit hnormalForms)

end SRG266.QuasiSymmetric
