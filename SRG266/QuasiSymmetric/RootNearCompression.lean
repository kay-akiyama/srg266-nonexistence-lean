/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.RootNearFreeDomain

/-!
# Compact coordinates for rooted first neighbourhoods

The mathematical mask `vertexFamilyMask near` uses the characteristic mask of
a triple as a bit position, so it occupies a sparse 2048-bit natural number.
Certificate files use the 56 triples on the eight vertices outside
`{0, 1, 2}` as consecutive bit positions instead.

This module defines that dictionary in Lean.  The order is the lexicographic
order on triples of `Fin 8` used by the certificate generator; adding three to
the vertices multiplies their characteristic mask by eight.  Certificate data
therefore remains compact, while every logical consumer expands it back to the
project's canonical `vertexFamilyMask` coordinates.
-/

namespace SRG266.QuasiSymmetric

/-- Characteristic masks of the 56 triples outside `{0, 1, 2}`, in
lexicographic order on their shifted `Fin 8` coordinates. -/
def rootNearCompressedCodes : List ℕ :=
  (List.range 8).flatMap fun a =>
    ((List.range 8).drop (a + 1)).flatMap fun b =>
      ((List.range 8).drop (b + 1)).map fun c =>
        8 * (2 ^ a ||| 2 ^ b ||| 2 ^ c)

theorem length_rootNearCompressedCodes : rootNearCompressedCodes.length = 56 := by
  decide +kernel

theorem nodup_rootNearCompressedCodes : rootNearCompressedCodes.Nodup := by
  decide +kernel

/-- The compact dictionary covers exactly the sparse positions accepted by
the canonical rooted search.  Only the order differs. -/
theorem rootNearCompressedCodes_toFinset :
    rootNearCompressedCodes.toFinset = (rootNearCodes 7).toFinset := by
  decide +kernel

/-- Expand consecutive bits along an arbitrary list of sparse positions. -/
def expandPositionMask (positions : List ℕ) (compressed : ℕ) : ℕ :=
  SRG266.Search.itemPositionsMask <|
    (positions.zipIdx.filter fun codeAndIndex =>
      compressed.testBit codeAndIndex.2).map Prod.fst

/-- Compress the bits at a list of sparse positions into consecutive bits. -/
def compressPositionMask (positions : List ℕ) (expanded : ℕ) : ℕ :=
  SRG266.Search.itemPositionsMask <|
    (positions.zipIdx.filter fun codeAndIndex =>
      expanded.testBit codeAndIndex.1).map Prod.snd

theorem compressPositionMask_lt (positions : List ℕ) (expanded : ℕ) :
    compressPositionMask positions expanded < 2 ^ positions.length := by
  apply SRG266.Search.itemPositionsMask_lt
  intro index hindex
  rw [List.mem_map] at hindex
  obtain ⟨entry, hentry, rfl⟩ := hindex
  have hzip := List.mem_zipIdx (List.mem_of_mem_filter hentry)
  simpa using hzip.2.1

/-- Expand a 56-bit rooted certificate mask into the canonical sparse mask. -/
def expandRootNearMask (compressed : ℕ) : ℕ :=
  expandPositionMask rootNearCompressedCodes compressed

/-- Compress a canonical sparse rooted-neighbourhood mask into 56 bits. -/
def compressRootNearMask (expanded : ℕ) : ℕ :=
  compressPositionMask rootNearCompressedCodes expanded

theorem testBit_expandPositionMask {positions : List ℕ} {compressed code : ℕ} :
    (expandPositionMask positions compressed).testBit code = true ↔
      ∃ index, (code, index) ∈ positions.zipIdx ∧
        compressed.testBit index = true := by
  rw [expandPositionMask, SRG266.Search.testBit_itemPositionsMask_iff]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨entry, ⟨hentry, hbit⟩, rfl⟩
    exact ⟨entry.2, hentry, hbit⟩
  · rintro ⟨index, hentry, hbit⟩
    exact ⟨(code, index), ⟨hentry, hbit⟩, rfl⟩

theorem testBit_compressPositionMask {positions : List ℕ} {expanded index : ℕ} :
    (compressPositionMask positions expanded).testBit index = true ↔
      ∃ code, (code, index) ∈ positions.zipIdx ∧
        expanded.testBit code = true := by
  rw [compressPositionMask, SRG266.Search.testBit_itemPositionsMask_iff]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨entry, ⟨hentry, hbit⟩, rfl⟩
    exact ⟨entry.1, hentry, hbit⟩
  · rintro ⟨code, hentry, hbit⟩
    exact ⟨(code, index), ⟨hentry, hbit⟩, rfl⟩

private theorem exists_zipIdx_of_mem {positions : List ℕ} {code : ℕ}
    (hcode : code ∈ positions) : ∃ index, (code, index) ∈ positions.zipIdx := by
  rw [← List.zipIdx_map_fst 0 positions] at hcode
  obtain ⟨entry, hentry, hfirst⟩ := List.mem_map.mp hcode
  exact ⟨entry.2, hfirst ▸ hentry⟩

private theorem zipIdx_index_unique_of_nodup {positions : List ℕ}
    (hnodup : positions.Nodup) {code i j : ℕ}
    (hi : (code, i) ∈ positions.zipIdx)
    (hj : (code, j) ∈ positions.zipIdx) : i = j := by
  have hi' := List.mem_zipIdx hi
  have hj' := List.mem_zipIdx hj
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hi' hj'
  exact (List.getElem_inj hnodup).mp (hi'.2.symm.trans hj'.2)

/-- Compressing an expanded compact mask recovers it, provided no bits occur
beyond the supplied dictionary. -/
theorem compressPositionMask_expandPositionMask {positions : List ℕ}
    (hnodup : positions.Nodup) {compressed : ℕ}
    (hlt : compressed < 2 ^ positions.length) :
    compressPositionMask positions (expandPositionMask positions compressed) =
      compressed := by
  apply Nat.eq_of_testBit_eq
  intro index
  apply Bool.eq_iff_iff.mpr
  rw [testBit_compressPositionMask]
  constructor
  · rintro ⟨code, hcode, hexpand⟩
    rw [testBit_expandPositionMask] at hexpand
    obtain ⟨other, hother, hbit⟩ := hexpand
    have hindex : index = other :=
      zipIdx_index_unique_of_nodup hnodup hcode hother
    simpa [hindex] using hbit
  · intro hbit
    have hindex : index < positions.length := by
      by_contra hnot
      have hpow : 2 ^ positions.length ≤ 2 ^ index :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hnot)
      have hfalse : compressed.testBit index = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hpow)
      rw [hfalse] at hbit
      exact Bool.noConfusion hbit
    let code := positions[index]
    have hentry : (code, index) ∈ positions.zipIdx := by
      rw [List.mem_iff_getElem]
      exact ⟨index, by simpa using hindex, by simp [code, List.getElem_zipIdx]⟩
    refine ⟨code, hentry, ?_⟩
    rw [testBit_expandPositionMask]
    exact ⟨index, hentry, hbit⟩

/-- Expanding a compression recovers every mask supported on the supplied
dictionary.  Duplicate dictionary entries would be harmless in this
direction. -/
theorem expandPositionMask_compressPositionMask {positions : List ℕ}
    {expanded : ℕ}
    (hsupport : ∀ code, expanded.testBit code = true → code ∈ positions) :
    expandPositionMask positions (compressPositionMask positions expanded) =
      expanded := by
  apply Nat.eq_of_testBit_eq
  intro code
  apply Bool.eq_iff_iff.mpr
  rw [testBit_expandPositionMask]
  constructor
  · rintro ⟨index, hentry, hcompressed⟩
    rw [testBit_compressPositionMask] at hcompressed
    obtain ⟨otherCode, hother, hbit⟩ := hcompressed
    have hentry' := List.mem_zipIdx hentry
    have hother' := List.mem_zipIdx hother
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hentry' hother'
    have : code = otherCode := hentry'.2.trans hother'.2.symm
    simpa [this] using hbit
  · intro hbit
    obtain ⟨index, hentry⟩ := exists_zipIdx_of_mem (hsupport code hbit)
    exact ⟨index, hentry,
      testBit_compressPositionMask.mpr ⟨code, hentry, hbit⟩⟩

theorem compressRootNearMask_expandRootNearMask {compressed : ℕ}
    (hlt : compressed < 2 ^ 56) :
    compressRootNearMask (expandRootNearMask compressed) = compressed := by
  apply compressPositionMask_expandPositionMask nodup_rootNearCompressedCodes
  simpa [length_rootNearCompressedCodes] using hlt

theorem compressRootNearMask_lt (expanded : ℕ) :
    compressRootNearMask expanded < 2 ^ 56 := by
  simpa [compressRootNearMask, length_rootNearCompressedCodes] using
    compressPositionMask_lt rootNearCompressedCodes expanded

/-- Every result of the complete rooted search is restored exactly after
compression and expansion. -/
theorem expandRootNearMask_compressRootNearMask_of_mem_rootNearFreeDomain
    {expanded : ℕ} (hmem : expanded ∈ rootNearFreeDomain 7) :
    expandRootNearMask (compressRootNearMask expanded) = expanded := by
  apply expandPositionMask_compressPositionMask
  intro code hbit
  have hsub : SRG266.Search.Submask expanded
      (SRG266.Search.itemPositionsMask (rootNearCodes 7)) := by
    exact SRG266.Search.submask_itemPositionsMask_of_mem_remainingItemDFS
      (guard := rootNearFreeRemainingOK 7)
      (accept := rootNearFreeAccept 7) hmem
  have hcode : code ∈ rootNearCodes 7 := by
    rw [← SRG266.Search.testBit_itemPositionsMask_iff]
    exact hsub code hbit
  have hfin : code ∈ (rootNearCodes 7).toFinset := by simpa using hcode
  rw [← rootNearCompressedCodes_toFinset] at hfin
  simpa using hfin

end SRG266.QuasiSymmetric
