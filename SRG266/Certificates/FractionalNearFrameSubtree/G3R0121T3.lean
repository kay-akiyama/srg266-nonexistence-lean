import SRG266.Certificates.FractionalNearFrameSubtree.G3R0121T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G3R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0121_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0121Mask fractionalNearFrameSubtreeG3R0121Witness
      fractionalNearFrameSubtreeG3R0121LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
