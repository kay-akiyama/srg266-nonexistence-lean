import SRG266.Certificates.FractionalNearFrameSubtree.G2R0179T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0179`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0179_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0179Mask fractionalNearFrameSubtreeG2R0179Witness
      fractionalNearFrameSubtreeG2R0179LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
