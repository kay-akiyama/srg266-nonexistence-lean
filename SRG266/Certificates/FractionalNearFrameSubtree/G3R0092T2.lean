import SRG266.Certificates.FractionalNearFrameSubtree.G3R0092T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G3R0092`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0092_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0092Mask fractionalNearFrameSubtreeG3R0092Witness
      fractionalNearFrameSubtreeG3R0092LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
