import SRG266.Certificates.FractionalNearFrameSubtree.G4R0023T3
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel-only obstruction for `G4R0023`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0023_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness
      (fractionalNearFrameSubtreeG4R0023Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0023Mask (fractionalNearFrameSubtreeG4R0023Endpoint 0)).drop 0).take 84)
      (31) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 12 12 fractionalNearFrameSubtreeG4R0023_s0000 (by simpa using fractionalNearFrameSubtreeG4R0023_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG4R0023_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG4R0023_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG4R0023_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG4R0023_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG4R0023_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG4R0023_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness
      (fractionalNearFrameSubtreeG4R0023Endpoint 0) (31) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG4R0023_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG4R0023_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness
      endpoint (fractionalNearFrameSubtreeG4R0023LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG4R0023_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG4R0023Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG4R0023Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG4R0023LowerBound, fractionalNearFrameSubtreeG4R0023LowerBoundTable, fractionalNearFrameSubtreeG4R0023Endpoint] using
      fractionalNearFrameSubtreeG4R0023_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness fractionalNearFrameSubtreeG4R0023LowerBoundTable 1 7 fractionalNearFrameSubtreeG4R0023_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness fractionalNearFrameSubtreeG4R0023LowerBoundTable 7 13 fractionalNearFrameSubtreeG4R0023_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness fractionalNearFrameSubtreeG4R0023LowerBoundTable 13 19 fractionalNearFrameSubtreeG4R0023_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness fractionalNearFrameSubtreeG4R0023LowerBoundTable 19 25 fractionalNearFrameSubtreeG4R0023_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0023 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG4R0023Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness fractionalNearFrameSubtreeG4R0023LowerBound fractionalNearFrameSubtreeG4R0023_lowerBound_valid
  decide +kernel

end SRG266.Certificates
