/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootBlockSystemDomain
import SRG266.QuasiSymmetric.CrossRowMaskDomain

/-!
# Complete second-level systems from packed rooted data

The second-level search can also be indexed without a mathematical
`GlobalDesignRoot`.  The root and near masks determine an executable list of
the remaining 140 triple codes.  A supplied numeric block function determines
the exact complete row domain.

At the genuine masks and genuine block function, the actual `24 × 140` cross
matrix occurs in `rootCrossSystemDomain`.  No generated enumeration or solver
conclusion is used in this transport theorem.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- Triple codes other than the root and its selected first neighbourhood. -/
def secondCodesOfMask (rootMask nearMask : ℕ) : List ℕ :=
  tripleCodes.filter fun code =>
    (code != rootMask) && (!nearMask.testBit code)

/-- Complete tagged cross-row domain for one row and its supplied block. -/
def crossChoiceDomainOfBlock (rootMask nearMask : ℕ)
    (blockOf : Finset (Fin 11) → ℕ) (U : Finset (Fin 11)) :
    List RootCrossMaskChoice :=
  (crossRowMaskDomain rootMask nearMask (vertexMask U) (blockOf U)).map
    fun m => ⟨vertexMask U, m⟩

/-- Complete second-level system domain for packed rooted data. -/
def rootCrossSystemDomain (rootMask nearMask : ℕ)
    (blockOf : Finset (Fin 11) → ℕ) : List (List RootCrossMaskChoice) :=
  let rows := nearRowsOfMask rootMask nearMask
  rootCrossMaskDFS rootMask (secondCodesOfMask rootMask nearMask) rows
    (crossChoiceDomainOfBlock rootMask nearMask blockOf)

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Every executable second code at the genuine masks decodes to a genuine
member of `zeroSecond`. -/
theorem secondCodesOfMask_actual_sound {code : ℕ}
    (hcode : code ∈ secondCodesOfMask (vertexMask R.root)
      (vertexFamilyMask R.near)) :
    ∃ X, X ∈ zeroSecond R.root R.near ∧ vertexMask X = code := by
  rw [secondCodesOfMask, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
    Bool.not_eq_true'] at hcode
  obtain ⟨htriple, hroot, hnear⟩ := hcode
  let X := verticesOfMask code
  have hlt : code < 2 ^ 11 := by
    have hc := (mem_tripleCodes.mp htriple).1
    norm_num at hc ⊢
    exact hc
  have hmask : vertexMask X = code := vertexMask_verticesOfMask hlt
  have hXt : X ∈ triples := by
    rw [mem_triples, ← popcount_vertexMask, hmask]
    exact (mem_tripleCodes.mp htriple).2
  have hXroot : X ≠ R.root := by
    intro h
    exact hroot (by rw [← hmask, h])
  have hXnear : X ∉ R.near := by
    intro h
    have hb := testBit_vertexFamilyMask_vertexMask R.near X
    rw [hmask, decide_eq_true h] at hb
    rw [hb] at hnear
    exact Bool.noConfusion hnear
  exact ⟨X, mem_zeroSecond.mpr ⟨hXt, hXroot, hXnear⟩, hmask⟩

/-- At the genuine block function, the actual cross matrix occurs in the
fully numeric second-level system domain. -/
theorem actualCrossMaskRows_mem_rootCrossSystemDomain :
    (nearRowsOfMask (vertexMask R.root) (vertexFamilyMask R.near)).map
        R.toGlobalZeroRoot.actualCrossMaskChoice ∈
      rootCrossSystemDomain (vertexMask R.root) (vertexFamilyMask R.near)
        R.actualBlockMask := by
  rw [rootCrossSystemDomain]
  apply R.toGlobalZeroRoot.actualCrossMaskRows_mem_rootCrossMaskDFS_rows
  · intro code hcode
    exact R.secondCodesOfMask_actual_sound hcode
  · exact R.nearRowsOfMask_actual_nodup
  · intro U hU
    exact R.nearRowsOfMask_actual_mem hU
  · exact R.nearRowsOfMask_actual_toFinset
  · intro U hU
    simpa [crossChoiceDomainOfBlock,
      GlobalDesignRoot.completeCrossMaskChoiceDomain] using
      R.actualCrossMaskChoice_mem_completeDomain hU

end GlobalDesignRoot

end SRG266.QuasiSymmetric
