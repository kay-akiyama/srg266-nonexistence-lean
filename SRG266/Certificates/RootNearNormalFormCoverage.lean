/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.RootCubicPrefixCoverage
import SRG266.Certificates.RootNearOrbitCoverage.Group0
import SRG266.Certificates.RootNearOrbitCoverage.Group1
import SRG266.Certificates.RootNearOrbitCoverage.Group2
import SRG266.Certificates.RootNearOrbitCoverage.Group3
import SRG266.Certificates.RootNearOrbitCoverage.Group4
import SRG266.Certificates.RootNearOrbitCoverage.Group5
import SRG266.QuasiSymmetric.RootOrbitTransport

/-!
# Normal-form coverage of rooted first neighbourhoods

This module composes the cubic root orbit cover with the six fixed-root near
orbit covers.  The coordinate transport and inverse permutation action are
proved in `RootOrbitTransport`; the result here is the exact mathematical
`RootNearNormalFormCover` consumed by the rooted cherry-cover reduction.
-/

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

private theorem rootNearRepresentatives_all_lt :
    rootNearRepresentatives.all (fun representative =>
      decide (representative < 2 ^ 56)) = true := by
  decide +kernel

private theorem rootNearRepresentative_lt {representative : ℕ}
    (hmem : representative ∈ rootNearRepresentatives) :
    representative < 2 ^ 56 := by
  have h := (List.all_eq_true.mp rootNearRepresentatives_all_lt)
    representative hmem
  simpa [decide_eq_true_eq] using h

/-- Dispatch a canonical cubic root to its corresponding fixed-root near
certificate. -/
private theorem canonicalNearOrbitCover {rootGraph mask : ℕ}
    (hroot : rootGraph ∈ rootGraphRepresentatives)
    (hlt : mask < 2 ^ 56) (hnear : IsNear8For rootGraph mask) :
    ∃ representative ∈ rootNearRepresentatives,
      ∃ permutationCode,
        PackedPerm8OK permutationCode ∧
          relabelEdgeMask8 permutationCode rootGraph = rootGraph ∧
            mask = relabelTripleMask8 permutationCode representative := by
  simp only [rootGraphRepresentatives, List.mem_cons, List.not_mem_nil,
    or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group0 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray0_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group1 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray1_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group2 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray2_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group3 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray3_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group4 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray4_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩
  · obtain ⟨representative, hrepresentative, permutationCode,
      hperm, hroot, hmask⟩ := near8_orbit_cover_group5 hlt hnear
    exact ⟨representative,
      rootNearRepresentativeArray5_mem representative hrepresentative,
      permutationCode, hperm, hroot, hmask⟩

/-- **Kernel-checked normal-form cover.**  Every labelled admissible rooted
first neighbourhood is carried, by a permutation fixing the root triple, to
one of the 2,752 listed representatives. -/
theorem rootNearNormalFormCover :
    RootNearNormalFormCover rootNearRepresentatives := by
  intro nearMask hmem
  let compact := compressRootNearMask nearMask
  have hcompactLt : compact < 2 ^ 56 := compressRootNearMask_lt nearMask
  have hexpand : expandRootNearMask compact = nearMask :=
    expandRootNearMask_compressRootNearMask_of_mem_rootNearFreeDomain hmem
  have hmem' := hmem
  change nearMask ∈ SRG266.Search.remainingItemDFS
    (rootNearFreeRemainingOK 7) (rootNearFreeAccept 7)
      (rootNearCodes 7) 0 at hmem'
  have hacceptRaw : rootNearFreeAccept 7 nearMask = true :=
    SRG266.Search.accept_of_mem_remainingItemDFS hmem'
  have haccept : rootNearFreeAccept 7 (expandRootNearMask compact) = true := by
    rw [hexpand]
    exact hacceptRaw
  have hcubic : IsCubic8 (reconstructedRootGraph8 compact) :=
    isCubic8_reconstructedRootGraph8_of_accept haccept
  have hnear : IsNear8For (reconstructedRootGraph8 compact) compact :=
    isNear8For_reconstructedRootGraph8_of_accept haccept
  obtain ⟨rootRepresentative, hrootRepresentative, permutationCode,
      hperm, hrootGraph⟩ :=
    cubic8_orbit_cover_prefix (reconstructedRootGraph8_lt compact) hcubic
  let inverseCode := inversePackedPerm8Code permutationCode hperm
  have hinverse : PackedPerm8OK inverseCode :=
    inversePackedPerm8Code_OK permutationCode hperm
  let canonicalMask := relabelTripleMask8 inverseCode compact
  have hcanonicalLt : canonicalMask < 2 ^ 56 :=
    relabelTripleMask8_lt inverseCode compact hinverse
  have hcanonicalNear : IsNear8For rootRepresentative canonicalMask := by
    have hrelabeled := hnear.relabel hinverse
    change IsNear8For
      (relabelEdgeMask8 inverseCode (reconstructedRootGraph8 compact))
      canonicalMask at hrelabeled
    rw [hrootGraph,
      relabelEdgeMask8_inverse permutationCode rootRepresentative hperm
        (rootGraphRepresentative_lt hrootRepresentative)] at hrelabeled
    exact hrelabeled
  obtain ⟨representative, hrepresentative, automorphismCode,
      hautomorphism, _, hcanonical⟩ :=
    canonicalNearOrbitCover hrootRepresentative hcanonicalLt hcanonicalNear
  let inverseAutomorphismCode :=
    inversePackedPerm8Code automorphismCode hautomorphism
  have hinverseAutomorphism :
      PackedPerm8OK inverseAutomorphismCode :=
    inversePackedPerm8Code_OK automorphismCode hautomorphism
  let σroot := packedPerm11Equiv inverseCode hinverse
  let σnear :=
    packedPerm11Equiv inverseAutomorphismCode hinverseAutomorphism
  let σ := σroot.trans σnear
  refine ⟨σ, ?_, representative, hrepresentative, ?_⟩
  · apply image_eq_self_of_mapsTo
    intro x hx
    simp [σ, σroot, σnear, packedPerm11Equiv,
      extendOff_apply_of_mem, hx]
  · have hrepresentativeLt : representative < 2 ^ 56 :=
      rootNearRepresentative_lt hrepresentative
    have hcanonicalInverse :
        relabelTripleMask8 inverseAutomorphismCode canonicalMask =
          representative := by
      rw [hcanonical,
        relabelTripleMask8_inverse automorphismCode representative
          hautomorphism hrepresentativeLt]
    dsimp only [σ, σroot, σnear]
    rw [relabelTripleFamilyMask_trans]
    rw [← hexpand]
    rw [relabelTripleFamilyMask_expandRootNearMask inverseCode compact hinverse]
    rw [relabelTripleFamilyMask_expandRootNearMask
      inverseAutomorphismCode canonicalMask hinverseAutomorphism]
    rw [hcanonicalInverse]

end SRG266.Certificates
