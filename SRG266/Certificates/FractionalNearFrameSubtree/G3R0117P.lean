import SRG266.Certificates.FractionalNearFrameSubtree.G3R0117T3
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Kernel-only obstruction for `G3R0117`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0117_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness
      (fractionalNearFrameSubtreeG3R0117Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0117Mask (fractionalNearFrameSubtreeG3R0117Endpoint 0)).drop 0).take 84)
      (-366) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 12 12 fractionalNearFrameSubtreeG3R0117_s0000 (by simpa using fractionalNearFrameSubtreeG3R0117_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG3R0117_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG3R0117_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG3R0117_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG3R0117_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG3R0117_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG3R0117_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness
      (fractionalNearFrameSubtreeG3R0117Endpoint 0) (-366) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG3R0117_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG3R0117_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness
      endpoint (fractionalNearFrameSubtreeG3R0117LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG3R0117_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG3R0117Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG3R0117Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG3R0117LowerBound, fractionalNearFrameSubtreeG3R0117LowerBoundTable, fractionalNearFrameSubtreeG3R0117Endpoint] using
      fractionalNearFrameSubtreeG3R0117_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness fractionalNearFrameSubtreeG3R0117LowerBoundTable 1 7 fractionalNearFrameSubtreeG3R0117_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness fractionalNearFrameSubtreeG3R0117LowerBoundTable 7 13 fractionalNearFrameSubtreeG3R0117_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness fractionalNearFrameSubtreeG3R0117LowerBoundTable 13 19 fractionalNearFrameSubtreeG3R0117_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness fractionalNearFrameSubtreeG3R0117LowerBoundTable 19 25 fractionalNearFrameSubtreeG3R0117_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG3R0117 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG3R0117Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG3R0117Mask fractionalNearFrameSubtreeG3R0117Witness fractionalNearFrameSubtreeG3R0117LowerBound fractionalNearFrameSubtreeG3R0117_lowerBound_valid
  decide +kernel

end SRG266.Certificates
