import SRG266.Certificates.FractionalNearFrameSubtree.G2R0565T3
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel-only obstruction for `G2R0565`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0565_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness
      (fractionalNearFrameSubtreeG2R0565Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0565Mask (fractionalNearFrameSubtreeG2R0565Endpoint 0)).drop 0).take 84)
      (4331) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 12 12 fractionalNearFrameSubtreeG2R0565_s0000 (by simpa using fractionalNearFrameSubtreeG2R0565_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG2R0565_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG2R0565_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG2R0565_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG2R0565_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG2R0565_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG2R0565_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness
      (fractionalNearFrameSubtreeG2R0565Endpoint 0) (4331) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG2R0565_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG2R0565_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness
      endpoint (fractionalNearFrameSubtreeG2R0565LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG2R0565_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG2R0565Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG2R0565Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG2R0565LowerBound, fractionalNearFrameSubtreeG2R0565LowerBoundTable, fractionalNearFrameSubtreeG2R0565Endpoint] using
      fractionalNearFrameSubtreeG2R0565_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness fractionalNearFrameSubtreeG2R0565LowerBoundTable 1 7 fractionalNearFrameSubtreeG2R0565_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness fractionalNearFrameSubtreeG2R0565LowerBoundTable 7 13 fractionalNearFrameSubtreeG2R0565_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness fractionalNearFrameSubtreeG2R0565LowerBoundTable 13 19 fractionalNearFrameSubtreeG2R0565_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness fractionalNearFrameSubtreeG2R0565LowerBoundTable 19 25 fractionalNearFrameSubtreeG2R0565_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG2R0565 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG2R0565Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG2R0565Mask fractionalNearFrameSubtreeG2R0565Witness fractionalNearFrameSubtreeG2R0565LowerBound fractionalNearFrameSubtreeG2R0565_lowerBound_valid
  decide +kernel

end SRG266.Certificates
