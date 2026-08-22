import SRG266.Certificates.FractionalNearFrameSubtree.G5R0006T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0006_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0006Mask fractionalNearFrameSubtreeG5R0006Witness
      fractionalNearFrameSubtreeG5R0006LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
