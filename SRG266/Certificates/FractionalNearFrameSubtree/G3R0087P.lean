import SRG266.Certificates.FractionalNearFrameSubtree.G3R0087T3
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel-only obstruction for `G3R0087`

Assembles the subtree shards of the empty endpoint and the folded
tail audits.  No `native_decide` and no `Float`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0087_e00_join :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness
      (fractionalNearFrameSubtreeG3R0087Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0087Mask (fractionalNearFrameSubtreeG3R0087Endpoint 0)).drop 0).take 84)
      (-46) := by
  have h1 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 12 12 fractionalNearFrameSubtreeG3R0087_s0000 (by simpa using fractionalNearFrameSubtreeG3R0087_s0012)
  have h2 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 24 12 h1 (by simpa using fractionalNearFrameSubtreeG3R0087_s0024)
  have h3 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 36 12 h2 (by simpa using fractionalNearFrameSubtreeG3R0087_s0036)
  have h4 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 48 12 h3 (by simpa using fractionalNearFrameSubtreeG3R0087_s0048)
  have h5 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 60 12 h4 (by simpa using fractionalNearFrameSubtreeG3R0087_s0060)
  have h6 := compactShellSubtreeLowerBoundOn_of_take_drop
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46)
    0 72 12 h5 (by simpa using fractionalNearFrameSubtreeG3R0087_s0072)
  simpa using h6

theorem fractionalNearFrameSubtreeG3R0087_e00_bound :
    IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness
      (fractionalNearFrameSubtreeG3R0087Endpoint 0) (-46) := by
  apply isCompactIndexedPairShellLowerBound_of_rootChildren
    (len := 84)
  · decide +kernel
  · decide +kernel
  · exact fractionalNearFrameSubtreeG3R0087_e00_join

/-- Every endpoint carries its tabulated lower bound. -/
theorem fractionalNearFrameSubtreeG3R0087_lowerBound_valid :
    ∀ endpoint, IsCompactIndexedPairShellLowerBound fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness
      endpoint (fractionalNearFrameSubtreeG3R0087LowerBound endpoint) := by
  intro endpoint
  have hlt : endpoint.val < 25 := by
    rw [← fractionalNearFrameSubtreeG3R0087_endpointCount]; exact endpoint.isLt
  rcases Nat.eq_zero_or_pos endpoint.val with hzero | hpos
  · have hendpoint : endpoint = fractionalNearFrameSubtreeG3R0087Endpoint 0 :=
      Fin.ext (by simpa [fractionalNearFrameSubtreeG3R0087Endpoint] using hzero)
    rw [hendpoint]
    simpa [fractionalNearFrameSubtreeG3R0087LowerBound, fractionalNearFrameSubtreeG3R0087LowerBoundTable, fractionalNearFrameSubtreeG3R0087Endpoint] using
      fractionalNearFrameSubtreeG3R0087_e00_bound
  · rcases Nat.lt_or_ge endpoint.val 7 with hw0 | hw0
    · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness fractionalNearFrameSubtreeG3R0087LowerBoundTable 1 7 fractionalNearFrameSubtreeG3R0087_t00 endpoint hpos hw0
    · rcases Nat.lt_or_ge endpoint.val 13 with hw1 | hw1
      · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness fractionalNearFrameSubtreeG3R0087LowerBoundTable 7 13 fractionalNearFrameSubtreeG3R0087_t01 endpoint hw0 hw1
      · rcases Nat.lt_or_ge endpoint.val 19 with hw2 | hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness fractionalNearFrameSubtreeG3R0087LowerBoundTable 13 19 fractionalNearFrameSubtreeG3R0087_t02 endpoint hw1 hw2
        · exact isCompactIndexedPairShellLowerBound_of_tailAuditRange fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness fractionalNearFrameSubtreeG3R0087LowerBoundTable 19 25 fractionalNearFrameSubtreeG3R0087_t03 endpoint hw2 hlt

/-- The obstruction, with only the three standard axioms. -/
theorem noCompactFractionalNearFrame_fractionalNearFrameSubtreeG3R0087 :
    NoCompactFractionalNearFrame fractionalNearFrameSubtreeG3R0087Mask := by
  apply noCompactFractionalNearFrame_of_indexedShellLowerBounds
    fractionalNearFrameSubtreeG3R0087Mask fractionalNearFrameSubtreeG3R0087Witness fractionalNearFrameSubtreeG3R0087LowerBound fractionalNearFrameSubtreeG3R0087_lowerBound_valid
  decide +kernel

end SRG266.Certificates
