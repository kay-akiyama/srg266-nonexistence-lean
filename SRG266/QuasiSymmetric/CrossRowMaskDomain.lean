/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.CubicMaskDomain
import SRG266.QuasiSymmetric.TripleCodes
import SRG266.QuasiSymmetric.RootCrossMaskSearch
import SRG266.Search.ItemMaskDFS

/-!
# Complete packed domains of rooted cross rows

For a fixed neighbour row and its cubic block, the exact pair law determines
how many of its 23 second columns contain each edge of `K₁₁`.  This module
enumerates those columns at the sparse characteristic-mask positions.  Both
the prefix predicate and its completeness theorem are kernel proved.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

set_option exponentiation.threshold 4096

/-- Population count of a packed family mask. -/
theorem popcount_vertexFamilyMask (S : Finset (Finset (Fin 11))) :
    popcount (vertexFamilyMask S) = S.card := by
  have h := popcount_and_vertexFamilyMask S S
  simpa using h

/-- Exact row demand for the pair represented by `e`. -/
def crossRowPairTarget (rootMask rowMask blockMask : ℕ) (e : Edge11) : ℕ :=
  let pair := vertexMask e.vertices
  if (rowMask &&& pair) == 0 then
    3 - (if popcount (rootMask &&& pair) == 2 then 1 else 0) -
      (if blockMask.testBit (edgeCoding.idx e) then 1 else 0)
  else 0

/-- Hereditary upper bounds while a cross row is assembled. -/
def crossRowMaskPrefixOK (rootMask rowMask blockMask m : ℕ) : Bool :=
  atMost 23 m &&
    edges.all fun e =>
      atMost (crossRowPairTarget rootMask rowMask blockMask e)
        (m &&& triplePairMask e)

/-- Exact leaf constraints for a cross row. -/
def crossRowMaskAccept (rootMask rowMask blockMask m : ℕ) : Bool :=
  (popcount m == 23) &&
    edges.all fun e =>
      popcount (m &&& triplePairMask e) ==
        crossRowPairTarget rootMask rowMask blockMask e

/-- Complete numeric domain of a cross row. -/
def crossRowMaskDomain (rootMask nearFamilyMask rowMask blockMask : ℕ) : List ℕ :=
  itemMaskDFS (crossRowMaskPrefixOK rootMask rowMask blockMask)
    (crossRowMaskAccept rootMask rowMask blockMask)
    (admissibleSecondCodes rootMask nearFamilyMask rowMask) 0

theorem crossRowMaskPrefixOK_hereditary (rootMask rowMask blockMask : ℕ) :
    Hereditary (crossRowMaskPrefixOK rootMask rowMask blockMask) := by
  intro m m' hsub hOK
  rw [crossRowMaskPrefixOK, Bool.and_eq_true] at hOK ⊢
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

theorem card_actualCrossColumns {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    (R.actualCrossColumns U).card = 23 := by
  exact R.cross_row_card hU

theorem inter_actualCrossColumns {U V : Finset (Fin 11)} :
    R.actualCrossColumns U ∩ R.actualCrossColumns V =
      (zeroSecond R.root R.near).filter fun X =>
        U ∈ R.cross X ∧ V ∈ R.cross X := by
  ext X
  simp [R.mem_actualCrossColumns, and_assoc, and_left_comm]

/-- The packed genuine row has the pair count prescribed by its block. -/
theorem actualCrossColumns_pairCount {U : Finset (Fin 11)} (hU : U ∈ R.near)
    (e : Edge11) :
    popcount (vertexFamilyMask (R.actualCrossColumns U) &&& triplePairMask e) =
      crossRowPairTarget (vertexMask R.root) (vertexMask U)
        (R.actualBlockMask U) e := by
  rw [triplePairMask, popcount_and_vertexFamilyMask]
  have hpairSet :
      R.actualCrossColumns U ∩ triplesThrough e.lo e.hi =
        (zeroSecond R.root R.near).filter fun X =>
          U ∈ R.cross X ∧ X ∈ triplesThrough e.lo e.hi := by
    ext X
    simp [R.mem_actualCrossColumns, and_assoc, and_left_comm]
  rw [hpairSet, crossRowPairTarget]
  have hlohi : e.lo ≠ e.hi := e.lo_lt_hi.ne
  by_cases hloU : e.lo ∈ U
  · have hmeetPos : vertexMask U &&& vertexMask e.vertices ≠ 0 := by
      intro hz
      have hp := congrArg popcount hz
      rw [popcount_and_vertexMask, popcount_zero] at hp
      have : e.lo ∈ U ∩ e.vertices :=
        Finset.mem_inter.mpr ⟨hloU, e.lo_mem⟩
      rw [Finset.card_eq_zero.mp hp] at this
      simp at this
    rw [if_neg (by simp [hmeetPos])]
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro X hX
    obtain ⟨hXsecond, hUX, hXpair⟩ := Finset.mem_filter.mp hX
    have hdisj := R.cross_supported hXsecond hUX
    have hloX := (mem_triplesThrough.mp hXpair).2.1
    have hloBoth : e.lo ∈ U ∩ X := Finset.mem_inter.mpr ⟨hloU, hloX⟩
    rw [Finset.card_eq_zero.mp hdisj] at hloBoth
    simp at hloBoth
  · by_cases hhiU : e.hi ∈ U
    · have hmeetPos : vertexMask U &&& vertexMask e.vertices ≠ 0 := by
        intro hz
        have hp := congrArg popcount hz
        rw [popcount_and_vertexMask, popcount_zero] at hp
        have : e.hi ∈ U ∩ e.vertices :=
          Finset.mem_inter.mpr ⟨hhiU, e.hi_mem⟩
        rw [Finset.card_eq_zero.mp hp] at this
        simp at this
      rw [if_neg (by simp [hmeetPos])]
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro X hX
      obtain ⟨hXsecond, hUX, hXpair⟩ := Finset.mem_filter.mp hX
      have hdisj := R.cross_supported hXsecond hUX
      have hhiX := (mem_triplesThrough.mp hXpair).2.2
      have hhiBoth : e.hi ∈ U ∩ X := Finset.mem_inter.mpr ⟨hhiU, hhiX⟩
      rw [Finset.card_eq_zero.mp hdisj] at hhiBoth
      simp at hhiBoth
    · have hrowZero : vertexMask U &&& vertexMask e.vertices = 0 := by
        apply eq_zero_of_popcount_eq_zero
        rw [popcount_and_vertexMask, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxv := Edge11.mem_vertices_iff.mp (Finset.mem_inter.mp hx).2
        rcases hxv with rfl | rfl
        · exact hloU (Finset.mem_inter.mp hx).1
        · exact hhiU (Finset.mem_inter.mp hx).1
      rw [if_pos (by simp [hrowZero])]
      have hexact := R.cross_pair_reconstruction hU hlohi hloU hhiU
      rw [actualBlockMask, edgeCoding.testBit_maskOf_idx]
      rw [popcount_and_vertexMask]
      have heq : e = Edge11.mk' hlohi :=
        Edge11.eq_of_mem_mem hlohi e.lo_mem e.hi_mem
      rw [← heq] at hexact
      by_cases hloR : e.lo ∈ R.root <;> by_cases hhiR : e.hi ∈ R.root <;>
        by_cases heB : e ∈ R.block U <;>
          simp [Edge11.vertices_eq, hloR, hhiR, heB, e.lo_lt_hi.ne] at hexact ⊢ <;>
          omega

/-- The genuine packed cross row passes every hereditary upper bound. -/
theorem crossRowMaskPrefixOK_actual {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    crossRowMaskPrefixOK (vertexMask R.root) (vertexMask U)
      (R.actualBlockMask U) (vertexFamilyMask (R.actualCrossColumns U)) = true := by
  rw [crossRowMaskPrefixOK, Bool.and_eq_true]
  constructor
  · rw [atMost_eq_true_iff, popcount_vertexFamilyMask, R.card_actualCrossColumns hU]
  · rw [List.all_eq_true]
    intro e he
    rw [atMost_eq_true_iff, R.actualCrossColumns_pairCount hU e]

/-- The genuine packed cross row satisfies the exact leaf equations. -/
theorem crossRowMaskAccept_actual {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    crossRowMaskAccept (vertexMask R.root) (vertexMask U)
      (R.actualBlockMask U) (vertexFamilyMask (R.actualCrossColumns U)) = true := by
  rw [crossRowMaskAccept, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, popcount_vertexFamilyMask, R.card_actualCrossColumns hU]
  · rw [List.all_eq_true]
    intro e he
    rw [beq_iff_eq, R.actualCrossColumns_pairCount hU e]

/-- Every set bit of the genuine row occurs among the sparse admissible items. -/
theorem actualCrossColumns_bit_covered {U : Finset (Fin 11)} {k : ℕ}
    (hk : (vertexFamilyMask (R.actualCrossColumns U)).testBit k = true) :
    k ∈ admissibleSecondCodes (vertexMask R.root)
      (vertexFamilyMask R.near) (vertexMask U) := by
  rw [testBit_vertexFamilyMask] at hk
  obtain ⟨X, hXrow, rfl⟩ := hk
  obtain ⟨hXsecond, hUX⟩ := R.mem_actualCrossColumns.mp hXrow
  exact vertexMask_mem_admissibleSecondCodes hXsecond
    (R.cross_supported hXsecond hUX)

/-- **Cross-row domain completeness.** -/
theorem actualCrossColumns_mem_crossRowMaskDomain
    {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    vertexFamilyMask (R.actualCrossColumns U) ∈
      crossRowMaskDomain (vertexMask R.root) (vertexFamilyMask R.near)
        (vertexMask U) (R.actualBlockMask U) := by
  rw [crossRowMaskDomain]
  apply itemMaskDFS_complete_of_hereditary
    (crossRowMaskPrefixOK_hereditary (vertexMask R.root)
      (vertexMask U) (R.actualBlockMask U))
  · intro k hk
    simp at hk
  · intro k hk _
    exact R.actualCrossColumns_bit_covered hk
  · exact R.crossRowMaskPrefixOK_actual hU
  · exact R.crossRowMaskAccept_actual hU

/-- Tagged row domain consumed by `rootCrossMaskDFS`. -/
def completeCrossMaskChoiceDomain (U : Finset (Fin 11)) :
    List RootCrossMaskChoice :=
  (crossRowMaskDomain (vertexMask R.root) (vertexFamilyMask R.near)
    (vertexMask U) (R.actualBlockMask U)).map fun m => ⟨vertexMask U, m⟩

/-- The genuine tagged row occurs in its complete generated domain. -/
theorem actualCrossMaskChoice_mem_completeDomain
    {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    R.toGlobalZeroRoot.actualCrossMaskChoice U ∈ R.completeCrossMaskChoiceDomain U := by
  rw [completeCrossMaskChoiceDomain, List.mem_map]
  refine ⟨vertexFamilyMask (R.actualCrossColumns U),
    R.actualCrossColumns_mem_crossRowMaskDomain hU, ?_⟩
  rfl

/-- The complete generated domains can be plugged directly into the packed
second-level DFS. -/
theorem actualCrossMaskRows_mem_completeRootCrossMaskDFS :
    R.near.toList.map R.toGlobalZeroRoot.actualCrossMaskChoice ∈
      rootCrossMaskDFS (vertexMask R.root)
        ((zeroSecond R.root R.near).toList.map vertexMask)
        R.near.toList R.completeCrossMaskChoiceDomain :=
  R.toGlobalZeroRoot.actualCrossMaskRows_mem_rootCrossMaskDFS
    R.completeCrossMaskChoiceDomain fun _ hU =>
      R.actualCrossMaskChoice_mem_completeDomain hU

end GlobalDesignRoot

end SRG266.QuasiSymmetric
