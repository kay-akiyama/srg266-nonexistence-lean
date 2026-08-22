import SRG266.Certificates.FractionalNearFrameSubtree.G1R0097T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G1R0097`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0097_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0097Mask fractionalNearFrameSubtreeG1R0097Witness
      fractionalNearFrameSubtreeG1R0097LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
