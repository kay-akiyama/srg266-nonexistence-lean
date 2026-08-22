/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootCrossSystemDomain

/-!
# Assembly of the complete rooted finite search

This file states the exact finite proposition whose checked refutation closes
the cherry-cover boundary.  It also proves the transport from an arbitrary
residual cherry obstruction to that proposition at the fixed root
`{0, 1, 2}`.

The three nested searches are:

1. `rootNearFreeDomain`, choosing the 24 first-neighbour triples;
2. `rootBlockSystemDomain`, choosing their 24 cubic blocks; and
3. `rootCrossSystemDomain`, choosing the complete 24-by-140 cross matrix.

All three completeness transports are ordinary Lean proofs. A certificate
needs only `RootedSearchRefutation 7`; no solver result crosses that boundary.
-/

namespace SRG266.QuasiSymmetric

/-- Recover a row-indexed block function from parallel row and block lists. -/
def blockOfRows : List (Finset (Fin 11)) → List ℕ →
    Finset (Fin 11) → ℕ
  | U :: rows, b :: blocks, X =>
      if X = U then b else blockOfRows rows blocks X
  | _, _, _ => 0

/-- Looking up a mapped block list recovers the original function on every
listed row. -/
theorem blockOfRows_map (rows : List (Finset (Fin 11)))
    (f : Finset (Fin 11) → ℕ) {U : Finset (Fin 11)} (hU : U ∈ rows) :
    blockOfRows rows (rows.map f) U = f U := by
  induction rows with
  | nil => simp at hU
  | cons V rows ih =>
      rw [List.map_cons, blockOfRows]
      by_cases hUV : U = V
      · subst U
        simp
      · rw [if_neg hUV]
        apply ih
        exact (List.mem_cons.mp hU).resolve_left hUV

/-- The cross-system search depends on a supplied block function only at its
listed near rows. -/
theorem rootCrossSystemDomain_congr_on_rows
    {rootMask nearMask : ℕ} {f g : Finset (Fin 11) → ℕ}
    (h : ∀ U ∈ nearRowsOfMask rootMask nearMask, f U = g U) :
    rootCrossSystemDomain rootMask nearMask f =
      rootCrossSystemDomain rootMask nearMask g := by
  have hdomains :
      (nearRowsOfMask rootMask nearMask).map
          (crossChoiceDomainOfBlock rootMask nearMask f) =
        (nearRowsOfMask rootMask nearMask).map
          (crossChoiceDomainOfBlock rootMask nearMask g) := by
    apply List.map_congr_left
    intro U hU
    rw [crossChoiceDomainOfBlock, crossChoiceDomainOfBlock, h U hU]
  rw [rootCrossSystemDomain, rootCrossSystemDomain, rootCrossMaskDFS,
    rootCrossMaskDFS, hdomains]

/-- The single finite statement left after all mathematical transport: every
first-level block system over every admissible near mask has an empty complete
second-level domain. -/
abbrev RootedSearchRefutation (rootMask : ℕ) : Prop :=
  ∀ nearMask, nearMask ∈ rootNearFreeDomain rootMask →
    ∀ blocks, blocks ∈ rootBlockSystemDomain rootMask nearMask →
      rootCrossSystemDomain rootMask nearMask
        (blockOfRows (nearRowsOfMask rootMask nearMask) blocks) = []

/-- The fixed root used to extract a rooted obstruction from a global design. -/
def fixedRoot012 : Finset (Fin 11) := {0, 1, 2}

theorem fixedRoot012_mem_triples : fixedRoot012 ∈ triples := by
  decide +kernel

theorem vertexMask_fixedRoot012 : vertexMask fixedRoot012 = 7 := by
  decide +kernel

/-- A checked refutation of the complete rooted finite search discharges the
last cherry-cover boundary directly. -/
theorem noResidualCherryCover_of_rootedSearchRefutation
    (h : RootedSearchRefutation 7) : NoResidualCherryCover := by
  apply noResidualCherryCover_of_isEmpty_globalDesign
  refine ⟨fun G => ?_⟩
  let R : GlobalDesignRoot :=
    G.toGlobalDesignRoot fixedRoot012 fixedRoot012_mem_triples
  have hroot : vertexMask R.root = 7 := by
    change vertexMask fixedRoot012 = 7
    exact vertexMask_fixedRoot012
  let nearMask := vertexFamilyMask R.near
  let rows := nearRowsOfMask (vertexMask R.root) nearMask
  let blocks := rows.map R.actualBlockMask
  have hnear : nearMask ∈ rootNearFreeDomain 7 := by
    rw [← hroot]
    exact R.actualNearMask_mem_rootNearFreeDomain
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
  have hempty := h nearMask hnear blocks hblocks
  have hrows : rows = nearRowsOfMask 7 nearMask := by
    dsimp [rows]
    rw [hroot]
  rw [hrows] at hcross
  rw [hempty] at hcross
  exact List.not_mem_nil hcross

end SRG266.QuasiSymmetric
