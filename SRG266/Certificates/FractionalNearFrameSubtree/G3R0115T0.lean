import SRG266.Certificates.FractionalNearFrameSubtree.G3R0115S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G3R0115`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0115_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0115Mask fractionalNearFrameSubtreeG3R0115Witness
      fractionalNearFrameSubtreeG3R0115LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
