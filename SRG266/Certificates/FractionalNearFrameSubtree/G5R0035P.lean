import SRG266.Certificates.FractionalNearFrameSubtree.G5R0035T3
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel-only obstruction for `G5R0035`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0035_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness
      (fractionalNearFrameSubtreeG5R0035Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0035Mask (fractionalNearFrameSubtreeG5R0035Endpoint 0)).drop 0).take 84)
      (-73) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 12 12 fractionalNearFrameSubtreeG5R0035_s0000 (by simpa using fractionalNearFrameSubtreeG5R0035_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG5R0035_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG5R0035_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG5R0035_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG5R0035_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG5R0035_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG5R0035_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness
      (fractionalNearFrameSubtreeG5R0035Endpoint 0) (-73) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG5R0035_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG5R0035_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness
      endpoint (fractionalNearFrameSubtreeG5R0035LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG5R0035_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG5R0035Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG5R0035Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG5R0035LowerBound, fractionalNearFrameSubtreeG5R0035LowerBoundTable, fractionalNearFrameSubtreeG5R0035Endpoint] using
      fractionalNearFrameSubtreeG5R0035_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness fractionalNearFrameSubtreeG5R0035LowerBoundTable 1 7 fractionalNearFrameSubtreeG5R0035_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness fractionalNearFrameSubtreeG5R0035LowerBoundTable 7 13 fractionalNearFrameSubtreeG5R0035_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness fractionalNearFrameSubtreeG5R0035LowerBoundTable 13 19 fractionalNearFrameSubtreeG5R0035_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness fractionalNearFrameSubtreeG5R0035LowerBoundTable 19 25 fractionalNearFrameSubtreeG5R0035_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG5R0035 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG5R0035Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness fractionalNearFrameSubtreeG5R0035LowerBound fractionalNearFrameSubtreeG5R0035_lowerBound_valid
  decide +kernel

end SRG266.Certificates
