import SRG266.Certificates.FractionalNearFrameSubtree.G2R0510S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0510`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0510_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0510Mask fractionalNearFrameSubtreeG2R0510Witness
      fractionalNearFrameSubtreeG2R0510LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
