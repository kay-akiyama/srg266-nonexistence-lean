/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootBlockMaskSearch
import SRG266.QuasiSymmetric.TripleCodes
import SRG266.Search.ItemMaskDFS
import SRG266.Search.RemainingItemDFS

/-!
# Complete packed domains for a rooted first neighbourhood

For a fixed root triple and its twelve-edge block, the local pair law
determines the multiplicity of every pair among the twenty-four disjoint
neighbour triples.  A pair outside the root occurs twice when it is a root
block edge and three times otherwise; pairs meeting the root occur zero times.

This module turns those equations into a sparse characteristic-mask search.
The mathematical first neighbourhood of every `GlobalDesignRoot` is proved to
occur in the generated domain.  Candidate generation is therefore outside the
trust boundary: later finite checks may consume `rootNearMaskDomain` directly.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

/-- Triple codes disjoint from a packed root triple. -/
def rootNearCodes (rootMask : ℕ) : List ℕ :=
  tripleCodes.filter fun code => (code &&& rootMask) == 0

/-- Required multiplicity of the pair represented by `e` in the rooted first
neighbourhood. -/
def rootNearPairTarget (rootMask rootBlockMask : ℕ) (e : Edge11) : ℕ :=
  if (rootMask &&& vertexMask e.vertices) == 0 then
    3 - (if rootBlockMask.testBit (edgeCoding.idx e) then 1 else 0)
  else 0

/-- Hereditary upper bounds while a first neighbourhood is assembled. -/
def rootNearMaskPrefixOK (rootMask rootBlockMask m : ℕ) : Bool :=
  atMost 24 m &&
    edges.all fun e =>
      atMost (rootNearPairTarget rootMask rootBlockMask e)
        (m &&& triplePairMask e)

/-- Exact leaf equations for a rooted first neighbourhood. -/
def rootNearMaskAccept (rootMask rootBlockMask m : ℕ) : Bool :=
  (popcount m == 24) &&
    edges.all fun e =>
      popcount (m &&& triplePairMask e) ==
        rootNearPairTarget rootMask rootBlockMask e

/-- Complete numeric domain of rooted first-neighbourhood masks. -/
def rootNearMaskDomain (rootMask rootBlockMask : ℕ) : List ℕ :=
  itemMaskDFS (rootNearMaskPrefixOK rootMask rootBlockMask)
    (rootNearMaskAccept rootMask rootBlockMask)
    (rootNearCodes rootMask) 0

/-- Suffix-aware feasibility: the partial mask obeys all upper bounds and the
union of the partial mask with every still-available item can meet all lower
bounds. -/
def rootNearRemainingOK (rootMask rootBlockMask : ℕ)
    (remaining : List ℕ) (m : ℕ) : Bool :=
  let possible := m ||| itemPositionsMask remaining
  rootNearMaskPrefixOK rootMask rootBlockMask m &&
    decide (24 ≤ popcount possible) &&
    edges.all fun e =>
      decide (rootNearPairTarget rootMask rootBlockMask e ≤
        popcount (possible &&& triplePairMask e))

/-- Execution-oriented rooted neighbourhood domain with suffix lower bounds. -/
def rootNearRemainingDomain (rootMask rootBlockMask : ℕ) : List ℕ :=
  remainingItemDFS (rootNearRemainingOK rootMask rootBlockMask)
    (rootNearMaskAccept rootMask rootBlockMask)
    (rootNearCodes rootMask) 0

theorem rootNearMaskPrefixOK_hereditary (rootMask rootBlockMask : ℕ) :
    Hereditary (rootNearMaskPrefixOK rootMask rootBlockMask) := by
  intro m m' hsub hOK
  rw [rootNearMaskPrefixOK, Bool.and_eq_true] at hOK ⊢
  constructor
  · rw [atMost_eq_true_iff] at hOK ⊢
    exact le_trans (popcount_mono hsub) hOK.1
  · rw [List.all_eq_true] at hOK ⊢
    intro e he
    have he' := hOK.2 e he
    rw [atMost_eq_true_iff] at he' ⊢
    exact le_trans
      (popcount_mono (hsub.and (Submask.refl (triplePairMask e)))) he'

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Population count of the packed genuine first neighbourhood. -/
theorem popcount_actualNearMask :
    popcount (vertexFamilyMask R.near) = 24 := by
  have h := popcount_and_vertexFamilyMask R.near R.near
  simpa [R.near_card] using h

/-- The packed genuine first neighbourhood has the pair multiplicities
prescribed by the root block. -/
theorem actualNearMask_pairCount (e : Edge11) :
    popcount (vertexFamilyMask R.near &&& triplePairMask e) =
      rootNearPairTarget (vertexMask R.root)
        (R.actualBlockMask R.root) e := by
  rw [triplePairMask, popcount_and_vertexFamilyMask, rootNearPairTarget]
  have hlohi : e.lo ≠ e.hi := e.lo_lt_hi.ne
  by_cases hloR : e.lo ∈ R.root
  · have hmeetPos : vertexMask R.root &&& vertexMask e.vertices ≠ 0 := by
      intro hz
      have hp := congrArg popcount hz
      rw [popcount_and_vertexMask, popcount_zero] at hp
      have : e.lo ∈ R.root ∩ e.vertices :=
        Finset.mem_inter.mpr ⟨hloR, e.lo_mem⟩
      rw [Finset.card_eq_zero.mp hp] at this
      simp at this
    rw [if_neg (by simpa using hmeetPos), Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hU
    obtain ⟨hUnear, hUpair⟩ := Finset.mem_inter.mp hU
    have hloU := (mem_triplesThrough.mp hUpair).2.1
    have hloBoth : e.lo ∈ R.root ∩ U :=
      Finset.mem_inter.mpr ⟨hloR, hloU⟩
    rw [Finset.card_eq_zero.mp (R.near_supported hUnear)] at hloBoth
    simp at hloBoth
  · by_cases hhiR : e.hi ∈ R.root
    · have hmeetPos : vertexMask R.root &&& vertexMask e.vertices ≠ 0 := by
        intro hz
        have hp := congrArg popcount hz
        rw [popcount_and_vertexMask, popcount_zero] at hp
        have : e.hi ∈ R.root ∩ e.vertices :=
          Finset.mem_inter.mpr ⟨hhiR, e.hi_mem⟩
        rw [Finset.card_eq_zero.mp hp] at this
        simp at this
      rw [if_neg (by simpa using hmeetPos), Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      obtain ⟨hUnear, hUpair⟩ := Finset.mem_inter.mp hU
      have hhiU := (mem_triplesThrough.mp hUpair).2.2
      have hhiBoth : e.hi ∈ R.root ∩ U :=
        Finset.mem_inter.mpr ⟨hhiR, hhiU⟩
      rw [Finset.card_eq_zero.mp (R.near_supported hUnear)] at hhiBoth
      simp at hhiBoth
    · have hrootZero : vertexMask R.root &&& vertexMask e.vertices = 0 := by
        apply eq_zero_of_popcount_eq_zero
        rw [popcount_and_vertexMask, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxv := Edge11.mem_vertices_iff.mp (Finset.mem_inter.mp hx).2
        rcases hxv with rfl | rfl
        · exact hloR (Finset.mem_inter.mp hx).1
        · exact hhiR (Finset.mem_inter.mp hx).1
      rw [if_pos (by simp [hrootZero])]
      have hexact := R.near_pair_reconstruction hlohi hloR hhiR
      have heq : e = Edge11.mk' hlohi :=
        Edge11.eq_of_mem_mem hlohi e.lo_mem e.hi_mem
      rw [← heq] at hexact
      rw [actualBlockMask, edgeCoding.testBit_maskOf_idx]
      by_cases heB : e ∈ R.block R.root <;>
        simp [heB] at hexact ⊢ <;> omega

/-- Every genuine near triple occurs among the sparse disjoint triple codes. -/
theorem actualNearMask_bit_covered {k : ℕ}
    (hk : (vertexFamilyMask R.near).testBit k = true) :
    k ∈ rootNearCodes (vertexMask R.root) := by
  rw [testBit_vertexFamilyMask] at hk
  obtain ⟨U, hUnear, rfl⟩ := hk
  rw [rootNearCodes, List.mem_filter]
  refine ⟨vertexMask_mem_tripleCodes (R.near_closed hUnear), ?_⟩
  rw [beq_iff_eq]
  apply eq_zero_of_popcount_eq_zero
  rw [popcount_and_vertexMask]
  simpa [Finset.inter_comm] using R.near_supported hUnear

/-- The genuine packed neighbourhood passes every hereditary upper bound. -/
theorem rootNearMaskPrefixOK_actual :
    rootNearMaskPrefixOK (vertexMask R.root) (R.actualBlockMask R.root)
      (vertexFamilyMask R.near) = true := by
  rw [rootNearMaskPrefixOK, Bool.and_eq_true]
  constructor
  · rw [atMost_eq_true_iff, R.popcount_actualNearMask]
  · rw [List.all_eq_true]
    intro e he
    rw [atMost_eq_true_iff, R.actualNearMask_pairCount e]

/-- The genuine packed neighbourhood satisfies the exact leaf equations. -/
theorem rootNearMaskAccept_actual :
    rootNearMaskAccept (vertexMask R.root) (R.actualBlockMask R.root)
      (vertexFamilyMask R.near) = true := by
  rw [rootNearMaskAccept, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, R.popcount_actualNearMask]
  · rw [List.all_eq_true]
    intro e he
    rw [beq_iff_eq, R.actualNearMask_pairCount e]

/-- Every partial branch contained in the genuine neighbourhood survives the
suffix-aware feasibility test as long as all missing genuine bits remain in
the suffix. -/
theorem rootNearRemainingOK_actual
    (remaining : List ℕ) (m : ℕ)
    (hsub : Submask m (vertexFamilyMask R.near))
    (hcover : ∀ k, (vertexFamilyMask R.near).testBit k = true →
      m.testBit k = false → k ∈ remaining) :
    rootNearRemainingOK (vertexMask R.root) (R.actualBlockMask R.root)
      remaining m = true := by
  have hpossible : Submask (vertexFamilyMask R.near)
      (m ||| itemPositionsMask remaining) :=
    submask_or_itemPositionsMask_of_cover hcover
  rw [rootNearRemainingOK, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact rootNearMaskPrefixOK_hereditary _ _ m
      (vertexFamilyMask R.near) hsub R.rootNearMaskPrefixOK_actual
  · rw [decide_eq_true_eq]
    calc
      24 = popcount (vertexFamilyMask R.near) := R.popcount_actualNearMask.symm
      _ ≤ popcount (m ||| itemPositionsMask remaining) := popcount_mono hpossible
  · rw [List.all_eq_true]
    intro e he
    rw [decide_eq_true_eq]
    calc
      rootNearPairTarget (vertexMask R.root) (R.actualBlockMask R.root) e =
          popcount (vertexFamilyMask R.near &&& triplePairMask e) :=
            (R.actualNearMask_pairCount e).symm
      _ ≤ popcount
          ((m ||| itemPositionsMask remaining) &&& triplePairMask e) :=
            popcount_mono
              (hpossible.and (Submask.refl (triplePairMask e)))

/-- **Rooted first-neighbourhood domain completeness.** -/
theorem actualNearMask_mem_rootNearMaskDomain :
    vertexFamilyMask R.near ∈
      rootNearMaskDomain (vertexMask R.root) (R.actualBlockMask R.root) := by
  rw [rootNearMaskDomain]
  apply itemMaskDFS_complete_of_hereditary
    (rootNearMaskPrefixOK_hereditary
      (vertexMask R.root) (R.actualBlockMask R.root))
  · intro k hk
    simp at hk
  · intro k hk _
    exact R.actualNearMask_bit_covered hk
  · exact R.rootNearMaskPrefixOK_actual
  · exact R.rootNearMaskAccept_actual

/-- **Suffix-aware rooted first-neighbourhood domain completeness.** -/
theorem actualNearMask_mem_rootNearRemainingDomain :
    vertexFamilyMask R.near ∈
      rootNearRemainingDomain (vertexMask R.root) (R.actualBlockMask R.root) := by
  rw [rootNearRemainingDomain]
  apply remainingItemDFS_complete
  · intro k hk
    simp at hk
  · intro k hk _
    exact R.actualNearMask_bit_covered hk
  · intro remaining m hsub hcover
    exact R.rootNearRemainingOK_actual remaining m hsub hcover
  · exact R.rootNearMaskAccept_actual

end GlobalDesignRoot

end SRG266.QuasiSymmetric
