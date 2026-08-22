import SRG266.Certificates.FractionalNearFrameSubtree.G5R0001S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G5R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0001_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0001Mask fractionalNearFrameSubtreeG5R0001Witness
      fractionalNearFrameSubtreeG5R0001LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
