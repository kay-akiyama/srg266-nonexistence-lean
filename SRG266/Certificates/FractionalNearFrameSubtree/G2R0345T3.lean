import SRG266.Certificates.FractionalNearFrameSubtree.G2R0345T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0345`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0345_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0345Mask fractionalNearFrameSubtreeG2R0345Witness
      fractionalNearFrameSubtreeG2R0345LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
