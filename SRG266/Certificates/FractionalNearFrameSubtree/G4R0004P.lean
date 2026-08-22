import SRG266.Certificates.FractionalNearFrameSubtree.G4R0004T3
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Kernel-only obstruction for `G4R0004`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0004_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness
      (fractionalNearFrameSubtreeG4R0004Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0004Mask (fractionalNearFrameSubtreeG4R0004Endpoint 0)).drop 0).take 84)
      (309) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 12 12 fractionalNearFrameSubtreeG4R0004_s0000 (by simpa using fractionalNearFrameSubtreeG4R0004_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG4R0004_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG4R0004_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG4R0004_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG4R0004_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG4R0004_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG4R0004_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness
      (fractionalNearFrameSubtreeG4R0004Endpoint 0) (309) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG4R0004_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG4R0004_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness
      endpoint (fractionalNearFrameSubtreeG4R0004LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG4R0004_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG4R0004Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG4R0004Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG4R0004LowerBound, fractionalNearFrameSubtreeG4R0004LowerBoundTable, fractionalNearFrameSubtreeG4R0004Endpoint] using
      fractionalNearFrameSubtreeG4R0004_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness fractionalNearFrameSubtreeG4R0004LowerBoundTable 1 7 fractionalNearFrameSubtreeG4R0004_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness fractionalNearFrameSubtreeG4R0004LowerBoundTable 7 13 fractionalNearFrameSubtreeG4R0004_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness fractionalNearFrameSubtreeG4R0004LowerBoundTable 13 19 fractionalNearFrameSubtreeG4R0004_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness fractionalNearFrameSubtreeG4R0004LowerBoundTable 19 25 fractionalNearFrameSubtreeG4R0004_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0004 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG4R0004Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG4R0004Mask fractionalNearFrameSubtreeG4R0004Witness fractionalNearFrameSubtreeG4R0004LowerBound fractionalNearFrameSubtreeG4R0004_lowerBound_valid
  decide +kernel

end SRG266.Certificates
