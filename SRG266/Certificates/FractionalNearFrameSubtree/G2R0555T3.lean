import SRG266.Certificates.FractionalNearFrameSubtree.G2R0555T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0555`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0555_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0555Mask fractionalNearFrameSubtreeG2R0555Witness
      fractionalNearFrameSubtreeG2R0555LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
