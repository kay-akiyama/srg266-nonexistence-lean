import SRG266.Certificates.FractionalNearFrameSubtree.G3R0058T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G3R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0058_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0058Mask fractionalNearFrameSubtreeG3R0058Witness
      fractionalNearFrameSubtreeG3R0058LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
