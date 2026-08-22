import SRG266.Certificates.FractionalNearFrameSubtree.G3R0082T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G3R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0082_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0082Mask fractionalNearFrameSubtreeG3R0082Witness
      fractionalNearFrameSubtreeG3R0082LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
