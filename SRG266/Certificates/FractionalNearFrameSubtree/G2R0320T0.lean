import SRG266.Certificates.FractionalNearFrameSubtree.G2R0320S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0320`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0320_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0320Mask fractionalNearFrameSubtreeG2R0320Witness
      fractionalNearFrameSubtreeG2R0320LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
