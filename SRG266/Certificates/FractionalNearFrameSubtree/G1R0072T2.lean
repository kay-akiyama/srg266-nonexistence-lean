import SRG266.Certificates.FractionalNearFrameSubtree.G1R0072T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G1R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0072_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0072Mask fractionalNearFrameSubtreeG1R0072Witness
      fractionalNearFrameSubtreeG1R0072LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
