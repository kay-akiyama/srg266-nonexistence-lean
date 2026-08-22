import SRG266.Certificates.FractionalNearFrameSubtree.G5R0069T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0069`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0069_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0069Mask fractionalNearFrameSubtreeG5R0069Witness
      fractionalNearFrameSubtreeG5R0069LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
