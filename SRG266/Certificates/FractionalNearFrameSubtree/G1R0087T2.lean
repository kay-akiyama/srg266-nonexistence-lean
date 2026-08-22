import SRG266.Certificates.FractionalNearFrameSubtree.G1R0087T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G1R0087`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0087_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0087Mask fractionalNearFrameSubtreeG1R0087Witness
      fractionalNearFrameSubtreeG1R0087LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
