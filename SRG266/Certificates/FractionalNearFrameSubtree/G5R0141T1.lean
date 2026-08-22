import SRG266.Certificates.FractionalNearFrameSubtree.G5R0141T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0141`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0141_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0141Mask fractionalNearFrameSubtreeG5R0141Witness
      fractionalNearFrameSubtreeG5R0141LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
