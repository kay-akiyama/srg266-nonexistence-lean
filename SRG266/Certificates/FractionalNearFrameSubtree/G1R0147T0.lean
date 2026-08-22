import SRG266.Certificates.FractionalNearFrameSubtree.G1R0147S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G1R0147`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0147_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0147Mask fractionalNearFrameSubtreeG1R0147Witness
      fractionalNearFrameSubtreeG1R0147LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
