import SRG266.Certificates.FractionalNearFrameSubtree.G1R0121T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0121_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0121Mask fractionalNearFrameSubtreeG1R0121Witness
      fractionalNearFrameSubtreeG1R0121LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
