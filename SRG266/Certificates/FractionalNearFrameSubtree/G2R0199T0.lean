import SRG266.Certificates.FractionalNearFrameSubtree.G2R0199S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0199`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0199_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0199Mask fractionalNearFrameSubtreeG2R0199Witness
      fractionalNearFrameSubtreeG2R0199LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
