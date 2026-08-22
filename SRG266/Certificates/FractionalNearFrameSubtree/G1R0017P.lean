import SRG266.Certificates.FractionalNearFrameSubtree.G1R0017T3
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Kernel-only obstruction for `G1R0017`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0017_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness
      (fractionalNearFrameSubtreeG1R0017Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0017Mask (fractionalNearFrameSubtreeG1R0017Endpoint 0)).drop 0).take 84)
      (-49) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 12 12 fractionalNearFrameSubtreeG1R0017_s0000 (by simpa using fractionalNearFrameSubtreeG1R0017_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG1R0017_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG1R0017_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG1R0017_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG1R0017_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG1R0017_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG1R0017_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness
      (fractionalNearFrameSubtreeG1R0017Endpoint 0) (-49) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG1R0017_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG1R0017_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness
      endpoint (fractionalNearFrameSubtreeG1R0017LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG1R0017_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG1R0017Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG1R0017Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG1R0017LowerBound, fractionalNearFrameSubtreeG1R0017LowerBoundTable, fractionalNearFrameSubtreeG1R0017Endpoint] using
      fractionalNearFrameSubtreeG1R0017_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness fractionalNearFrameSubtreeG1R0017LowerBoundTable 1 7 fractionalNearFrameSubtreeG1R0017_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness fractionalNearFrameSubtreeG1R0017LowerBoundTable 7 13 fractionalNearFrameSubtreeG1R0017_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness fractionalNearFrameSubtreeG1R0017LowerBoundTable 13 19 fractionalNearFrameSubtreeG1R0017_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness fractionalNearFrameSubtreeG1R0017LowerBoundTable 19 25 fractionalNearFrameSubtreeG1R0017_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG1R0017 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG1R0017Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG1R0017Mask fractionalNearFrameSubtreeG1R0017Witness fractionalNearFrameSubtreeG1R0017LowerBound fractionalNearFrameSubtreeG1R0017_lowerBound_valid
  decide +kernel

end SRG266.Certificates
