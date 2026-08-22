import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Data
import SRG266.QuasiSymmetric.FractionalNearFrameRhsRangeAudit

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-! # Start-hybrid endpoint sum [5, 9) for group 2 representative 0 -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameGroup2Representative0000_endpoint01 :
    CompactIndexedStartHybridEndpointSumOn
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      (((compactIndexedStartHybridEndpointIndices
        fractionalNearFrameGroup2Representative0000.nearMask).drop 5).take 4)
      (-1107) := by
  apply compactIndexedStartHybridEndpointSumOn_of_audit
  decide +kernel

end SRG266.Certificates
