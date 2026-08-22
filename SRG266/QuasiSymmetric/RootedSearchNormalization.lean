/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootedSearchAssembly
import SRG266.QuasiSymmetric.TripleFamilyRelabel
import SRG266.QuasiSymmetric.RootNearCompression

/-!
# Normal-form reduction for the rooted finite search

The raw domain `rootNearFreeDomain 7` contains all labelled first
neighbourhoods.  Certificate generation instead works with the 2,752 rooted
orbits under permutations stabilising `{0,1,2}`.  This file cleanly separates
the two finite obligations:

* `RootNearNormalFormCover reps`: every raw admissible near mask has an
  explicit relabelling into `reps`;
* `RootedRepresentativeRefutation reps`: every first-level block system over
  every listed representative has an empty complete cross-system domain.

Both statements are finite and executable.  Together they imply
`NoResidualCherryCover` by a kernel-proved transport.
-/

namespace SRG266.QuasiSymmetric

/-- Every admissible labelled near mask can be relabelled, while fixing the
root set, to the expansion of a listed 56-bit representative. -/
abbrev RootNearNormalFormCover (reps : List ℕ) : Prop :=
  ∀ nearMask, nearMask ∈ rootNearFreeDomain 7 →
    ∃ σ : Equiv.Perm (Fin 11),
      fixedRoot012.image σ = fixedRoot012 ∧
        ∃ compressed ∈ reps,
          relabelTripleFamilyMask σ nearMask =
            expandRootNearMask compressed

/-- The expansion of every listed representative has no complete rooted
extension. -/
abbrev RootedRepresentativeRefutation (reps : List ℕ) : Prop :=
  ∀ compressed, compressed ∈ reps →
    ∀ blocks, blocks ∈
      rootBlockSystemDomain 7 (expandRootNearMask compressed) →
      rootCrossSystemDomain 7 (expandRootNearMask compressed)
        (blockOfRows
          (nearRowsOfMask 7 (expandRootNearMask compressed)) blocks) = []

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Refute one genuine rooted design once the finite second-level result is
known at its exact near mask. -/
theorem false_of_rootedRepresentativeCase
    (hroot : vertexMask R.root = 7)
    (hrefute : ∀ blocks,
      blocks ∈ rootBlockSystemDomain 7 (vertexFamilyMask R.near) →
        rootCrossSystemDomain 7 (vertexFamilyMask R.near)
          (blockOfRows
            (nearRowsOfMask 7 (vertexFamilyMask R.near)) blocks) = []) :
    False := by
  let nearMask := vertexFamilyMask R.near
  let rows := nearRowsOfMask (vertexMask R.root) nearMask
  let blocks := rows.map R.actualBlockMask
  have hblocks : blocks ∈ rootBlockSystemDomain 7 nearMask := by
    rw [← hroot]
    exact R.actualBlockMasks_mem_rootBlockSystemDomain
  have hcross :
      rows.map R.toGlobalZeroRoot.actualCrossMaskChoice ∈
        rootCrossSystemDomain 7 nearMask
          (blockOfRows rows blocks) := by
    rw [← hroot]
    rw [rootCrossSystemDomain_congr_on_rows (f := blockOfRows rows blocks)
      (g := R.actualBlockMask) (by
        intro U hU
        exact blockOfRows_map rows R.actualBlockMask hU)]
    exact R.actualCrossMaskRows_mem_rootCrossSystemDomain
  have hempty := hrefute blocks hblocks
  have hrows : rows = nearRowsOfMask 7 nearMask := by
    dsimp [rows]
    rw [hroot]
  rw [hrows] at hcross
  rw [hempty] at hcross
  exact List.not_mem_nil hcross

end GlobalDesignRoot

/-- A finite orbit cover plus finite representative refutations discharge the
cherry-cover boundary. -/
theorem noResidualCherryCover_of_normalizedRootedSearch
    (reps : List ℕ)
    (hcover : RootNearNormalFormCover reps)
    (hrefute : RootedRepresentativeRefutation reps) :
    NoResidualCherryCover := by
  apply noResidualCherryCover_of_isEmpty_globalDesign
  refine ⟨fun G => ?_⟩
  let R : GlobalDesignRoot :=
    G.toGlobalDesignRoot fixedRoot012 fixedRoot012_mem_triples
  have hroot : vertexMask R.root = 7 := by
    change vertexMask fixedRoot012 = 7
    exact vertexMask_fixedRoot012
  have hnear : vertexFamilyMask R.near ∈ rootNearFreeDomain 7 := by
    rw [← hroot]
    exact R.actualNearMask_mem_rootNearFreeDomain
  obtain ⟨σ, hfix, compressed, hrep, hexpand⟩ :=
    hcover (vertexFamilyMask R.near) hnear
  let G' := G.relabel σ
  let R' : GlobalDesignRoot :=
    G'.toGlobalDesignRoot fixedRoot012 fixedRoot012_mem_triples
  have hroot' : vertexMask R'.root = 7 := by
    change vertexMask fixedRoot012 = 7
    exact vertexMask_fixedRoot012
  have hnearRelabel :
      vertexFamilyMask R'.near =
        relabelTripleFamilyMask σ (vertexFamilyMask R.near) := by
    change vertexFamilyMask ((G.relabel σ).disjointFrom fixedRoot012) =
      relabelTripleFamilyMask σ
        (vertexFamilyMask (G.disjointFrom fixedRoot012))
    exact G.vertexFamilyMask_disjointFrom_relabel_of_fixed σ fixedRoot012 hfix
  have hnearExpanded :
      vertexFamilyMask R'.near = expandRootNearMask compressed := by
    rw [hnearRelabel, hexpand]
  apply R'.false_of_rootedRepresentativeCase hroot'
  intro blocks hblocks
  rw [hnearExpanded] at hblocks ⊢
  exact hrefute compressed hrep blocks hblocks

end SRG266.QuasiSymmetric
