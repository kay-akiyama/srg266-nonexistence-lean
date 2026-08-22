import SRG266.Certificates.FractionalNearFrameSubtree.G5R0111T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0111_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0111Mask fractionalNearFrameSubtreeG5R0111Witness
      fractionalNearFrameSubtreeG5R0111LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
