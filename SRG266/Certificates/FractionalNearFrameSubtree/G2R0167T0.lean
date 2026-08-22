import SRG266.Certificates.FractionalNearFrameSubtree.G2R0167S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0167`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0167_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0167Mask fractionalNearFrameSubtreeG2R0167Witness
      fractionalNearFrameSubtreeG2R0167LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
