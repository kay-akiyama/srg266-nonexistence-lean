/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.RootBlockMaskSearch
import SRG266.QuasiSymmetric.VertexMask
import SRG266.Search.ItemMaskDFS

/-!
# Complete packed domains of rooted cubic blocks

The first-level row domain consists of the 12-edge graphs which avoid the root
block, isolate the row triple, and have degree three at every other vertex.
`cubicMaskDomain` enumerates exactly these masks with the proved hereditary
`maskDFS`: prefixes may not use a forbidden edge, may not touch an isolated
vertex, and may not exceed degree three.

`GlobalDesignRoot.actualBlockMask_mem_cubicMaskDomain` is the required domain
completeness theorem.  It removes candidate generation from the external trust
boundary.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

/-- Degree of a packed edge set at a numbered vertex. -/
def packedDegree (m v : ℕ) : ℕ := popcount (m &&& starMask v)

/-- Hereditary prefix constraints for a cubic row. -/
def cubicMaskPrefixOK (isolateMask rootBlockMask m : ℕ) : Bool :=
  ((m &&& rootBlockMask) == 0) &&
    ((List.range 11).all fun v =>
      if isolateMask.testBit v then (m &&& starMask v) == 0
      else atMost 3 (m &&& starMask v))

/-- Exact leaf constraints for a cubic row. -/
def cubicMaskAccept (isolateMask m : ℕ) : Bool :=
  (popcount m == 12) &&
    ((List.range 11).all fun v =>
      packedDegree m v == if isolateMask.testBit v then 0 else 3)

/-- The numeric endpoint mask agrees with the decoded edge. -/
theorem edgeVertexMask_eq : ∀ i : Fin 55,
    edgeVertexMask i.val = vertexMask (edgeAt i).vertices := by
  decide +kernel

/-- Edge positions allowed by the root block and isolated row vertices. -/
def cubicEdgePositions (isolateMask rootBlockMask : ℕ) : List ℕ :=
  (List.range 55).filter fun i =>
    (!rootBlockMask.testBit i) && ((edgeVertexMask i &&& isolateMask) == 0)

/-- Complete domain of cubic masks for one rooted row. -/
def cubicMaskDomain (isolateMask rootBlockMask : ℕ) : List ℕ :=
  itemMaskDFS (cubicMaskPrefixOK isolateMask rootBlockMask)
    (cubicMaskAccept isolateMask) (cubicEdgePositions isolateMask rootBlockMask) 0

/-- Prefix feasibility is inherited by deleting edges. -/
theorem cubicMaskPrefixOK_hereditary (isolateMask rootBlockMask : ℕ) :
    Hereditary (cubicMaskPrefixOK isolateMask rootBlockMask) := by
  intro m m' hsub hOK
  rw [cubicMaskPrefixOK, Bool.and_eq_true] at hOK ⊢
  constructor
  · rw [beq_iff_eq] at hOK ⊢
    have hz : Submask (m &&& rootBlockMask) 0 :=
      (hsub.and (Submask.refl rootBlockMask)).trans
        (hOK.1 ▸ Submask.refl 0)
    exact hz.eq_zero
  · rw [List.all_eq_true] at hOK ⊢
    intro v hv
    have hv' := hOK.2 v hv
    by_cases hiso : isolateMask.testBit v = true
    · rw [if_pos hiso, beq_iff_eq] at hv' ⊢
      have hz : Submask (m &&& starMask v) 0 :=
        (hsub.and (Submask.refl (starMask v))).trans
          (hv' ▸ Submask.refl 0)
      exact hz.eq_zero
    · rw [if_neg hiso] at hv' ⊢
      rw [atMost_eq_true_iff] at hv' ⊢
      exact le_trans (popcount_mono (hsub.and (Submask.refl (starMask v)))) hv'

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Packed degree is the ordinary arc degree of a genuine block. -/
theorem packedDegree_actualBlockMask (U : Finset (Fin 11)) (v : Fin 11) :
    packedDegree (R.actualBlockMask U) v.val = arcDegree (R.block U) v := by
  have hstar : edgeCoding.maskOf (Edge11.star v) = starMask v.val := by
    rw [← edgesOfMask_starMask v]
    exact edgeCoding.maskOf_edgesOfMask (starMask_lt v)
  rw [packedDegree, actualBlockMask, ← hstar,
    edgeCoding.popcount_and_maskOf, card_inter_star]

/-- Every genuine neighbour block passes the hereditary prefix predicate. -/
theorem cubicMaskPrefixOK_actualBlockMask {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    cubicMaskPrefixOK (vertexMask U) (R.actualBlockMask R.root)
      (R.actualBlockMask U) = true := by
  rw [cubicMaskPrefixOK, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, actualBlockMask, actualBlockMask]
    apply eq_zero_of_popcount_eq_zero
    rw [edgeCoding.popcount_and_maskOf]
    simpa [Finset.inter_comm] using R.root_near_disjoint hU
  · rw [List.all_eq_true]
    intro v hv
    have hv11 : v < 11 := List.mem_range.mp hv
    let fv : Fin 11 := ⟨v, hv11⟩
    rw [show (vertexMask U).testBit v = decide (fv ∈ U) by
      exact testBit_vertexMask_val U fv]
    by_cases hvU : fv ∈ U
    · rw [decide_eq_true hvU, if_pos rfl, beq_iff_eq]
      apply eq_zero_of_popcount_eq_zero
      rw [← packedDegree, R.packedDegree_actualBlockMask U fv]
      exact R.near_block_isolates hU hvU
    · rw [decide_eq_false hvU, if_neg Bool.false_ne_true]
      rw [atMost_eq_true_iff]
      change packedDegree (R.actualBlockMask U) fv.val ≤ 3
      rw [R.packedDegree_actualBlockMask U fv, R.near_block_cubic hU fv hvU]

/-- Every genuine neighbour block satisfies the exact cubic leaf predicate. -/
theorem cubicMaskAccept_actualBlockMask {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    cubicMaskAccept (vertexMask U) (R.actualBlockMask U) = true := by
  rw [cubicMaskAccept, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, actualBlockMask, edgeCoding.popcount_maskOf]
    exact R.near_block_card hU
  · rw [List.all_eq_true]
    intro v hv
    have hv11 : v < 11 := List.mem_range.mp hv
    let fv : Fin 11 := ⟨v, hv11⟩
    rw [show (vertexMask U).testBit v = decide (fv ∈ U) by
      exact testBit_vertexMask_val U fv]
    by_cases hvU : fv ∈ U
    · rw [decide_eq_true hvU, if_pos rfl, beq_iff_eq,
        R.packedDegree_actualBlockMask U fv, R.near_block_isolates hU hvU]
    · rw [decide_eq_false hvU, if_neg Bool.false_ne_true, beq_iff_eq,
        R.packedDegree_actualBlockMask U fv, R.near_block_cubic hU fv hvU]

/-- The genuine root block satisfies the same exact cubic predicate, with the
root triple as its isolation mask. -/
theorem cubicMaskAccept_actualRootBlockMask :
    cubicMaskAccept (vertexMask R.root) (R.actualBlockMask R.root) = true := by
  rw [cubicMaskAccept, Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq, actualBlockMask, edgeCoding.popcount_maskOf]
    exact R.root_block_card
  · rw [List.all_eq_true]
    intro v hv
    have hv11 : v < 11 := List.mem_range.mp hv
    let fv : Fin 11 := ⟨v, hv11⟩
    rw [show (vertexMask R.root).testBit v = decide (fv ∈ R.root) by
      exact testBit_vertexMask_val R.root fv]
    by_cases hvR : fv ∈ R.root
    · rw [decide_eq_true hvR, if_pos rfl, beq_iff_eq,
        R.packedDegree_actualBlockMask R.root fv, R.root_block_isolates hvR]
    · rw [decide_eq_false hvR, if_neg Bool.false_ne_true, beq_iff_eq,
        R.packedDegree_actualBlockMask R.root fv, R.root_block_cubic fv hvR]

/-- **Cubic-domain completeness.**  The generated domain contains every
genuine neighbour block mask. -/
theorem actualBlockMask_mem_cubicMaskDomain {U : Finset (Fin 11)} (hU : U ∈ R.near) :
    R.actualBlockMask U ∈
      cubicMaskDomain (vertexMask U) (R.actualBlockMask R.root) := by
  rw [cubicMaskDomain]
  apply itemMaskDFS_complete_of_hereditary
    (cubicMaskPrefixOK_hereditary (vertexMask U) (R.actualBlockMask R.root))
  · intro k hk
    simp at hk
  · intro k hk _
    have hk55 : k < 55 := by
      by_contra hnot
      have hz : (R.actualBlockMask U).testBit k = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (edgeCoding.maskOf_lt (R.block U))
            (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hnot)))
      rw [hz] at hk
      exact Bool.noConfusion hk
    let i : Fin 55 := ⟨k, hk55⟩
    have heU : edgeAt i ∈ R.block U := by
      have ht := R.actualBlockMask_testBit U i
      rw [hk] at ht
      simpa using ht
    have hrootFalse : (R.actualBlockMask R.root).testBit k = false := by
      rcases Bool.eq_false_or_eq_true ((R.actualBlockMask R.root).testBit k) with htrue | hfalse
      · have heRoot : edgeAt i ∈ R.block R.root := by
          have ht := R.actualBlockMask_testBit R.root i
          rw [htrue] at ht
          simpa using ht
        have heBoth : edgeAt i ∈ R.block R.root ∩ R.block U :=
          Finset.mem_inter.mpr ⟨heRoot, heU⟩
        have hempty := Finset.card_eq_zero.mp (R.root_near_disjoint hU)
        rw [hempty] at heBoth
        simp at heBoth
      · exact hfalse
    have hisolateZero : edgeVertexMask k &&& vertexMask U = 0 := by
      rw [edgeVertexMask_eq i]
      apply eq_zero_of_popcount_eq_zero
      rw [popcount_and_vertexMask, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxEdge := (Finset.mem_inter.mp hx).1
      have hxU := (Finset.mem_inter.mp hx).2
      have heFilter : edgeAt i ∈ (R.block U).filter fun e => x ∈ e.vertices :=
        Finset.mem_filter.mpr ⟨heU, hxEdge⟩
      have hpos : 0 < arcDegree (R.block U) x :=
        Finset.card_pos.mpr ⟨edgeAt i, heFilter⟩
      rw [R.near_block_isolates hU hxU] at hpos
      omega
    rw [cubicEdgePositions, List.mem_filter]
    exact ⟨List.mem_range.mpr hk55, by simp [hrootFalse, hisolateZero]⟩
  · exact R.cubicMaskPrefixOK_actualBlockMask hU
  · exact R.cubicMaskAccept_actualBlockMask hU

/-- The packed first-level DFS may use `cubicMaskDomain` directly, with no
remaining domain-completeness hypothesis. -/
theorem actualBlockMasks_mem_completeRootBlockMaskDFS :
    R.near.toList.map R.actualBlockMask ∈
      rootBlockMaskDFS R.actualRootEdgeTarget R.near.toList
        (fun U => cubicMaskDomain (vertexMask U) (R.actualBlockMask R.root)) :=
  R.actualBlockMasks_mem_rootBlockMaskDFS _ fun _ hU =>
    R.actualBlockMask_mem_cubicMaskDomain hU

end GlobalDesignRoot

end SRG266.QuasiSymmetric
