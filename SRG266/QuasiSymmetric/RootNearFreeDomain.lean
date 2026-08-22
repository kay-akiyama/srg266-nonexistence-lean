/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.CubicMaskDomain
import SRG266.QuasiSymmetric.RootNearMaskDomain

/-!
# Rooted first neighbourhoods without a supplied root block

The root block is determined by its first neighbourhood: among pairs outside
the root, precisely the pairs occurring twice are root-block edges.  This file
uses that observation to remove the six-way root-block classification from the
top level of the finite search.

The free domain chooses only twenty-four disjoint triples.  It requires every
off-root pair to occur two or three times, reconstructs the low-pair graph, and
checks that graph is cubic on the eight vertices outside the root.  Every
`GlobalDesignRoot` maps into this domain by ordinary Lean theorems.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

/-- The low-pair graph reconstructed from a packed first neighbourhood. -/
def reconstructedRootBlock (rootMask nearMask : ℕ) : Finset Edge11 :=
  Finset.univ.filter fun e =>
    rootMask &&& vertexMask e.vertices = 0 ∧
      popcount (nearMask &&& triplePairMask e) = 2

/-- Packed coordinates of the reconstructed low-pair graph. -/
def reconstructedRootBlockMask (rootMask nearMask : ℕ) : ℕ :=
  edgeCoding.maskOf (reconstructedRootBlock rootMask nearMask)

/-- The admissible multiplicities for one pair of a free rooted
neighbourhood. -/
def rootNearFreePairAccept (rootMask m : ℕ) (e : Edge11) : Bool :=
  let count := popcount (m &&& triplePairMask e)
  if (rootMask &&& vertexMask e.vertices) == 0 then
    (count == 2) || (count == 3)
  else count == 0

/-- Hereditary upper bounds for a free rooted neighbourhood. -/
def rootNearFreePrefixOK (rootMask m : ℕ) : Bool :=
  atMost 24 m &&
    edges.all fun e =>
      atMost (if (rootMask &&& vertexMask e.vertices) == 0 then 3 else 0)
        (m &&& triplePairMask e)

/-- Exact leaf constraints, including cubicity of the reconstructed block. -/
def rootNearFreeAccept (rootMask m : ℕ) : Bool :=
  (popcount m == 24) &&
    (edges.all fun e => rootNearFreePairAccept rootMask m e) &&
    cubicMaskAccept rootMask (reconstructedRootBlockMask rootMask m)

/-- Suffix-aware feasibility for the free rooted search. -/
def rootNearFreeRemainingOK (rootMask : ℕ) (remaining : List ℕ) (m : ℕ) : Bool :=
  let possible := m ||| itemPositionsMask remaining
  rootNearFreePrefixOK rootMask m &&
    decide (24 ≤ popcount possible) &&
    edges.all fun e =>
      if (rootMask &&& vertexMask e.vertices) == 0 then
        decide (2 ≤ popcount (possible &&& triplePairMask e))
      else true

/-- Root-block-free complete search domain. -/
def rootNearFreeDomain (rootMask : ℕ) : List ℕ :=
  remainingItemDFS (rootNearFreeRemainingOK rootMask)
    (rootNearFreeAccept rootMask) (rootNearCodes rootMask) 0

theorem rootNearFreePrefixOK_hereditary (rootMask : ℕ) :
    Hereditary (rootNearFreePrefixOK rootMask) := by
  intro m m' hsub hOK
  rw [rootNearFreePrefixOK, Bool.and_eq_true] at hOK ⊢
  constructor
  · rw [atMost_eq_true_iff] at hOK ⊢
    exact le_trans (popcount_mono hsub) hOK.1
  · rw [List.all_eq_true] at hOK ⊢
    intro e he
    have he' := hOK.2 e he
    rw [atMost_eq_true_iff] at he' ⊢
    exact le_trans
      (popcount_mono (hsub.and (Submask.refl (triplePairMask e)))) he'

/-- A zero intersection between a vertex mask and an edge mask says exactly
that both endpoints lie outside the vertex set. -/
theorem vertexMask_and_edge_eq_zero_iff (T : Finset (Fin 11)) (e : Edge11) :
    vertexMask T &&& vertexMask e.vertices = 0 ↔
      e.lo ∉ T ∧ e.hi ∉ T := by
  constructor
  · intro hz
    constructor
    · intro hlo
      have hp := congrArg popcount hz
      rw [popcount_and_vertexMask, popcount_zero] at hp
      have hmem : e.lo ∈ T ∩ e.vertices :=
        Finset.mem_inter.mpr ⟨hlo, e.lo_mem⟩
      rw [Finset.card_eq_zero.mp hp] at hmem
      simp at hmem
    · intro hhi
      have hp := congrArg popcount hz
      rw [popcount_and_vertexMask, popcount_zero] at hp
      have hmem : e.hi ∈ T ∩ e.vertices :=
        Finset.mem_inter.mpr ⟨hhi, e.hi_mem⟩
      rw [Finset.card_eq_zero.mp hp] at hmem
      simp at hmem
  · rintro ⟨hlo, hhi⟩
    apply eq_zero_of_popcount_eq_zero
    rw [popcount_and_vertexMask, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxv := Edge11.mem_vertices_iff.mp (Finset.mem_inter.mp hx).2
    rcases hxv with rfl | rfl
    · exact hlo (Finset.mem_inter.mp hx).1
    · exact hhi (Finset.mem_inter.mp hx).1

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- A root-block edge cannot meet the isolated root triple. -/
theorem rootBlock_endpoint_not_mem {e : Edge11} (he : e ∈ R.block R.root)
    {v : Fin 11} (hv : v ∈ e.vertices) : v ∉ R.root := by
  intro hvR
  have heFilter : e ∈ (R.block R.root).filter fun f => v ∈ f.vertices :=
    Finset.mem_filter.mpr ⟨he, hv⟩
  have hpos : 0 < arcDegree (R.block R.root) v :=
    Finset.card_pos.mpr ⟨e, heFilter⟩
  rw [R.root_block_isolates hvR] at hpos
  omega

/-- The low-pair reconstruction is exactly the genuine root block. -/
theorem reconstructedRootBlock_eq_actual :
    reconstructedRootBlock (vertexMask R.root) (vertexFamilyMask R.near) =
      R.block R.root := by
  ext e
  simp only [reconstructedRootBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [vertexMask_and_edge_eq_zero_iff, triplePairMask,
    popcount_and_vertexFamilyMask]
  have hlohi : e.lo ≠ e.hi := e.lo_lt_hi.ne
  have heq : e = Edge11.mk' hlohi :=
    Edge11.eq_of_mem_mem hlohi e.lo_mem e.hi_mem
  constructor
  · rintro ⟨⟨hloR, hhiR⟩, htwo⟩
    exact heq.symm ▸
      (R.mem_rootBlock_iff_near_pair_eq_two hlohi hloR hhiR).mpr htwo
  · intro he
    have hloR := R.rootBlock_endpoint_not_mem he e.lo_mem
    have hhiR := R.rootBlock_endpoint_not_mem he e.hi_mem
    exact ⟨⟨hloR, hhiR⟩,
      (R.mem_rootBlock_iff_near_pair_eq_two hlohi hloR hhiR).mp
        (heq ▸ he)⟩

/-- Packed reconstruction likewise equals the genuine packed root block. -/
theorem reconstructedRootBlockMask_eq_actual :
    reconstructedRootBlockMask (vertexMask R.root) (vertexFamilyMask R.near) =
      R.actualBlockMask R.root := by
  rw [reconstructedRootBlockMask, R.reconstructedRootBlock_eq_actual,
    actualBlockMask]

/-- Each genuine pair multiplicity satisfies the free two-or-three law. -/
theorem rootNearFreePairAccept_actual (e : Edge11) :
    rootNearFreePairAccept (vertexMask R.root)
      (vertexFamilyMask R.near) e = true := by
  have hcount := R.actualNearMask_pairCount e
  rw [rootNearPairTarget] at hcount
  simp only [rootNearFreePairAccept]
  by_cases hz : vertexMask R.root &&& vertexMask e.vertices = 0
  · rw [if_pos (by simp [hz])] at hcount ⊢
    rw [hcount]
    by_cases he : (R.actualBlockMask R.root).testBit
        (edgeCoding.idx e) = true
    · simp [he]
    · simp [he]
  · rw [if_neg (by simpa using hz)] at hcount ⊢
    simp [hcount]

/-- The genuine family passes the free hereditary prefix bounds. -/
theorem rootNearFreePrefixOK_actual :
    rootNearFreePrefixOK (vertexMask R.root)
      (vertexFamilyMask R.near) = true := by
  rw [rootNearFreePrefixOK, Bool.and_eq_true]
  constructor
  · rw [atMost_eq_true_iff, R.popcount_actualNearMask]
  · rw [List.all_eq_true]
    intro e he
    have hp := R.rootNearFreePairAccept_actual e
    rw [rootNearFreePairAccept] at hp
    by_cases hz : vertexMask R.root &&& vertexMask e.vertices = 0
    · rw [if_pos (by simp [hz])] at hp ⊢
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hp
      rw [atMost_eq_true_iff]
      omega
    · rw [if_neg (by simpa using hz)] at hp ⊢
      rw [beq_iff_eq] at hp
      simp [atMost_eq_true_iff, hp]

/-- The genuine family satisfies the free exact leaf constraints. -/
theorem rootNearFreeAccept_actual :
    rootNearFreeAccept (vertexMask R.root)
      (vertexFamilyMask R.near) = true := by
  rw [rootNearFreeAccept, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [beq_iff_eq, R.popcount_actualNearMask]
  · rw [List.all_eq_true]
    intro e he
    exact R.rootNearFreePairAccept_actual e
  · rw [R.reconstructedRootBlockMask_eq_actual]
    exact R.cubicMaskAccept_actualRootBlockMask

/-- Every partial genuine branch survives the root-block-free suffix guard. -/
theorem rootNearFreeRemainingOK_actual
    (remaining : List ℕ) (m : ℕ)
    (hsub : Submask m (vertexFamilyMask R.near))
    (hcover : ∀ k, (vertexFamilyMask R.near).testBit k = true →
      m.testBit k = false → k ∈ remaining) :
    rootNearFreeRemainingOK (vertexMask R.root) remaining m = true := by
  have hpossible : Submask (vertexFamilyMask R.near)
      (m ||| itemPositionsMask remaining) :=
    submask_or_itemPositionsMask_of_cover hcover
  rw [rootNearFreeRemainingOK, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact rootNearFreePrefixOK_hereditary _ m
      (vertexFamilyMask R.near) hsub R.rootNearFreePrefixOK_actual
  · rw [decide_eq_true_eq]
    calc
      24 = popcount (vertexFamilyMask R.near) := R.popcount_actualNearMask.symm
      _ ≤ popcount (m ||| itemPositionsMask remaining) := popcount_mono hpossible
  · rw [List.all_eq_true]
    intro e he
    by_cases hz : vertexMask R.root &&& vertexMask e.vertices = 0
    · rw [if_pos (by simp [hz]), decide_eq_true_eq]
      have hp := R.rootNearFreePairAccept_actual e
      rw [rootNearFreePairAccept, if_pos (by simp [hz]), Bool.or_eq_true,
        beq_iff_eq, beq_iff_eq] at hp
      calc
        2 ≤ popcount (vertexFamilyMask R.near &&& triplePairMask e) := by omega
        _ ≤ popcount
            ((m ||| itemPositionsMask remaining) &&& triplePairMask e) :=
              popcount_mono
                (hpossible.and (Submask.refl (triplePairMask e)))
    · rw [if_neg (by simpa using hz)]

/-- **Root-block-free first-neighbourhood completeness.** -/
theorem actualNearMask_mem_rootNearFreeDomain :
    vertexFamilyMask R.near ∈ rootNearFreeDomain (vertexMask R.root) := by
  rw [rootNearFreeDomain]
  apply remainingItemDFS_complete
  · intro k hk
    simp at hk
  · intro k hk _
    exact R.actualNearMask_bit_covered hk
  · intro remaining m hsub hcover
    exact R.rootNearFreeRemainingOK_actual remaining m hsub hcover
  · exact R.rootNearFreeAccept_actual

end GlobalDesignRoot

end SRG266.QuasiSymmetric
