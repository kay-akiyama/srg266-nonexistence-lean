import SRG266.Certificates.FractionalNearFrameSubtree.G1R0138T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0138`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0138_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0138Mask fractionalNearFrameSubtreeG1R0138Witness
      fractionalNearFrameSubtreeG1R0138LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
