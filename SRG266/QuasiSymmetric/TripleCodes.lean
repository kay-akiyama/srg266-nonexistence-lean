/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.VertexMask
import SRG266.QuasiSymmetric.GlobalZeroRoot

/-!
# Executable characteristic-mask coordinates for all triples

The list `tripleCodes` is obtained without a lookup table: filter the numbers
below `2^11` by population count three.  It is executable and every
mathematical three-subset maps into it.  Further filters remove the root, its
first neighbourhood, and triples meeting a chosen row.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- Population count of a vertex characteristic mask. -/
theorem popcount_vertexMask (s : Finset (Fin 11)) :
    popcount (vertexMask s) = s.card := by
  have h := popcount_and_vertexMask s s
  simpa using h

/-- The executable list of all 165 characteristic masks of triples. -/
def tripleCodes : List ℕ :=
  (List.range 2048).filter fun code => popcount code == 3

theorem mem_tripleCodes {code : ℕ} :
    code ∈ tripleCodes ↔ code < 2048 ∧ popcount code = 3 := by
  simp [tripleCodes, beq_iff_eq]

/-- Every mathematical triple occurs in the executable code list. -/
theorem vertexMask_mem_tripleCodes {T : Finset (Fin 11)} (hT : T ∈ triples) :
    vertexMask T ∈ tripleCodes := by
  rw [mem_tripleCodes]
  constructor
  · have h := vertexMask_lt T
    norm_num at h ⊢
    exact h
  · rw [popcount_vertexMask, mem_triples.mp hT]

/-- Numeric second columns: triples other than the root and first
neighbourhood, additionally disjoint from the chosen row mask. -/
def admissibleSecondCodes (rootMask nearFamilyMask rowMask : ℕ) : List ℕ :=
  tripleCodes.filter fun code =>
    (code != rootMask) && (!nearFamilyMask.testBit code) &&
      ((code &&& rowMask) == 0)

/-- A genuine second triple disjoint from a row occurs in the numeric list. -/
theorem vertexMask_mem_admissibleSecondCodes
    {root U X : Finset (Fin 11)} {near : Finset (Finset (Fin 11))}
    (hX : X ∈ zeroSecond root near) (hdisj : (U ∩ X).card = 0) :
    vertexMask X ∈
      admissibleSecondCodes (vertexMask root) (vertexFamilyMask near) (vertexMask U) := by
  obtain ⟨hXt, hXroot, hXnear⟩ := mem_zeroSecond.mp hX
  rw [admissibleSecondCodes, List.mem_filter]
  refine ⟨vertexMask_mem_tripleCodes hXt, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  refine ⟨⟨fun h => hXroot (vertexMask_injective h), ?_⟩, ?_⟩
  · rw [Bool.not_eq_true', testBit_vertexFamilyMask_vertexMask,
      decide_eq_false_iff_not]
    exact hXnear
  apply eq_zero_of_popcount_eq_zero
  rw [popcount_and_vertexMask]
  simpa [Finset.inter_comm] using hdisj

/-- The packed family of triples through the endpoints of an edge. -/
def triplePairMask (e : Edge11) : ℕ :=
  vertexFamilyMask (triplesThrough e.lo e.hi)

/-- On a triple, the pair-family bit records containment of both endpoints. -/
theorem triplePairMask_testBit {X : Finset (Fin 11)} (hX : X ∈ triples)
    (e : Edge11) :
    (triplePairMask e).testBit (vertexMask X) =
      decide (e.lo ∈ X ∧ e.hi ∈ X) := by
  rw [triplePairMask, testBit_vertexFamilyMask_vertexMask]
  apply decide_eq_decide.mpr
  rw [mem_triplesThrough]
  simp [hX]

end SRG266.QuasiSymmetric
