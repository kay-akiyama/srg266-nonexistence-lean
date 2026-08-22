import SRG266.Certificates.FractionalNearFrameSubtree.G5R0013T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0013_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0013Mask fractionalNearFrameSubtreeG5R0013Witness
      fractionalNearFrameSubtreeG5R0013LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
