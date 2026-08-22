/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootNearFreeDomain

/-!
# Complete first-level block systems from a packed near family

This module removes the mathematical `GlobalDesignRoot` from the executable
parameters of the first-level block search.  A packed near family determines
both its row list and its reconstructed root block.  The exact edge targets
are then numeric functions of those two masks.

For every genuine rooted design, its twenty-four packed neighbour blocks occur
in `rootBlockSystemDomain` at its genuine near mask.  Thus a later chunked
certificate may be indexed solely by numeric near masks.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

/-- Executable duplicate-free row list selected by a packed near mask. -/
def nearRowsOfMask (rootMask nearMask : ℕ) : List (Finset (Fin 11)) :=
  (((rootNearCodes rootMask).filter fun code => nearMask.testBit code).map
    verticesOfMask).dedup

/-- Numeric edge replication target for a reconstructed rooted block. -/
def packedRootEdgeTarget (rootMask rootBlockMask : ℕ) (i : ℕ) : ℕ :=
  if _ : i < 55 then
    if rootBlockMask.testBit i then 0
    else 6 + popcount (edgeVertexMask i &&& rootMask)
  else 0

/-- Complete simple first-level domain for one packed near family.  The cubic
row generator is the proved specification `cubicMaskDomain`; faster generators
may replace it after proving inclusion. -/
def rootBlockSystemDomain (rootMask nearMask : ℕ) : List (List ℕ) :=
  let rootBlockMask := reconstructedRootBlockMask rootMask nearMask
  let rows := nearRowsOfMask rootMask nearMask
  rootBlockMaskDFS (packedRootEdgeTarget rootMask rootBlockMask)
    rows
    (fun U => cubicMaskDomain (vertexMask U) rootBlockMask)

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Decoding the genuine packed near mask recovers exactly the genuine near
family. -/
theorem nearRowsOfMask_actual_toFinset :
    (nearRowsOfMask (vertexMask R.root)
      (vertexFamilyMask R.near)).toFinset = R.near := by
  ext U
  simp only [List.mem_toFinset, nearRowsOfMask, List.mem_dedup,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨code, ⟨hcode, hbit⟩, rfl⟩
    have hlt : code < 2 ^ 11 := by
      have hc := (mem_tripleCodes.mp (List.mem_filter.mp hcode).1).1
      norm_num at hc ⊢
      exact hc
    have hmask := vertexMask_verticesOfMask hlt
    rw [← hmask, testBit_vertexFamilyMask_vertexMask] at hbit
    simpa using hbit
  · intro hU
    refine ⟨vertexMask U, ⟨?_, ?_⟩, verticesOfMask_vertexMask U⟩
    · apply R.actualNearMask_bit_covered
      rw [testBit_vertexFamilyMask_vertexMask]
      exact decide_eq_true hU
    · rw [testBit_vertexFamilyMask_vertexMask]
      exact decide_eq_true hU

theorem nearRowsOfMask_actual_nodup :
    (nearRowsOfMask (vertexMask R.root)
      (vertexFamilyMask R.near)).Nodup := by
  exact List.nodup_dedup _

theorem nearRowsOfMask_actual_mem {U : Finset (Fin 11)}
    (hU : U ∈ nearRowsOfMask (vertexMask R.root)
      (vertexFamilyMask R.near)) : U ∈ R.near := by
  have hset := R.nearRowsOfMask_actual_toFinset
  rw [← hset, List.mem_toFinset]
  exact hU

/-- The numeric edge target agrees extensionally with the target supplied by
the mathematical rooted design. -/
theorem packedRootEdgeTarget_actual :
    packedRootEdgeTarget (vertexMask R.root) (R.actualBlockMask R.root) =
      R.actualRootEdgeTarget := by
  funext i
  by_cases hi : i < 55
  · let fi : Fin 55 := ⟨i, hi⟩
    rw [packedRootEdgeTarget, dif_pos hi, R.actualRootEdgeTarget_fin fi,
      rootEdgeTarget]
    have hbit := R.actualBlockMask_testBit R.root fi
    change (R.actualBlockMask R.root).testBit i =
      decide (edgeAt fi ∈ R.block R.root) at hbit
    rw [edgeVertexMask_eq fi, popcount_and_vertexMask]
    by_cases he : edgeAt fi ∈ R.block R.root
    · rw [decide_eq_true he] at hbit
      simp [hbit, he]
    · rw [decide_eq_false he] at hbit
      simp [hbit, he, Finset.inter_comm]
  · rw [packedRootEdgeTarget, dif_neg hi, GlobalDesignRoot.actualRootEdgeTarget,
      dif_neg hi]

/-- **Packed first-level completeness with no mathematical search
parameters.** -/
theorem actualBlockMasks_mem_rootBlockSystemDomain :
    (nearRowsOfMask (vertexMask R.root) (vertexFamilyMask R.near)).map
        R.actualBlockMask ∈
      rootBlockSystemDomain (vertexMask R.root) (vertexFamilyMask R.near) := by
  have hroot := R.reconstructedRootBlockMask_eq_actual
  have htarget := R.packedRootEdgeTarget_actual
  rw [rootBlockSystemDomain, hroot, htarget]
  apply R.actualBlockMasks_mem_rootBlockMaskDFS_rows
  · exact R.nearRowsOfMask_actual_nodup
  · intro U hU
    exact R.nearRowsOfMask_actual_mem hU
  · exact R.nearRowsOfMask_actual_toFinset
  · intro U hU
    exact R.actualBlockMask_mem_cubicMaskDomain hU

end GlobalDesignRoot

end SRG266.QuasiSymmetric
