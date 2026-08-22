import SRG266.Certificates.FractionalNearFrameSubtree.G2R0227T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0227`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0227_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0227Mask fractionalNearFrameSubtreeG2R0227Witness
      fractionalNearFrameSubtreeG2R0227LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
