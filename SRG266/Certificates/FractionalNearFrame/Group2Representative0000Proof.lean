import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Start
import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Endpoint00
import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Endpoint01
import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Endpoint02

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel-only fractional near-frame pilot

This module assembles the bounded start-shell and endpoint-sum shards for group
2 representative 0.  The pair-weight array is projected from the generated
data module; no local column, descent path, endpoint coefficient, or native
audit reaches the theorem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameGroup2Representative0000_endpointSum :
    CompactIndexedStartHybridEndpointSumOn
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      (compactIndexedStartHybridEndpointIndices
        fractionalNearFrameGroup2Representative0000.nearMask) (-2526) := by
  have htail : CompactIndexedStartHybridEndpointSumOn
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      ((compactIndexedStartHybridEndpointIndices
        fractionalNearFrameGroup2Representative0000.nearMask).drop 5)
      (-3195) := by
    simpa using compactIndexedStartHybridEndpointSumOn_of_take_drop
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      ((compactIndexedStartHybridEndpointIndices
        fractionalNearFrameGroup2Representative0000.nearMask).drop 5)
      4 (-1107) (-2088)
      fractionalNearFrameGroup2Representative0000_endpoint01
      fractionalNearFrameGroup2Representative0000_endpoint02
  simpa using compactIndexedStartHybridEndpointSumOn_of_take_drop
    fractionalNearFrameGroup2Representative0000.nearMask
    fractionalNearFrameGroup2Representative0000Witness
    (compactIndexedStartHybridEndpointIndices
      fractionalNearFrameGroup2Representative0000.nearMask)
    5 669 (-3195)
    fractionalNearFrameGroup2Representative0000_endpoint00 htail

theorem fractionalNearFrameGroup2Representative0000_rhs :
    compactKernelIndexedStartHybridFarkasRhsDot
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness < 0 := by
  apply compactKernelIndexedStartHybridFarkasRhsDot_lt_of_endpoint_sum
    fractionalNearFrameGroup2Representative0000.nearMask
    fractionalNearFrameGroup2Representative0000Witness (-2526)
    fractionalNearFrameGroup2Representative0000_endpointSum
  decide +kernel

theorem fractionalNearFrameGroup2Representative0000_noFrame :
    NoCompactFractionalNearFrame 236306569216131 := by
  rw [← fractionalNearFrameGroup2Representative0000_nearMask]
  exact noCompactFractionalNearFrame_of_indexedStartHybridPairFarkas
    fractionalNearFrameGroup2Representative0000.nearMask
    fractionalNearFrameGroup2Representative0000Witness
    fractionalNearFrameGroup2Representative0000_startBound
    fractionalNearFrameGroup2Representative0000_rhs

end SRG266.Certificates
