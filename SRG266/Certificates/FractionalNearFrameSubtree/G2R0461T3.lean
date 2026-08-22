import SRG266.Certificates.FractionalNearFrameSubtree.G2R0461T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0461`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0461_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0461Mask fractionalNearFrameSubtreeG2R0461Witness
      fractionalNearFrameSubtreeG2R0461LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
