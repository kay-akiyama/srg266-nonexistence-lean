import SRG266.Certificates.FractionalNearFrameSubtree.G3R0110T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G3R0110`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0110_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0110Mask fractionalNearFrameSubtreeG3R0110Witness
      fractionalNearFrameSubtreeG3R0110LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
