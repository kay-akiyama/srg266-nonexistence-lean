import SRG266.Certificates.FractionalNearFrameSubtree.G2R0106T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0106`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0106_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0106Mask fractionalNearFrameSubtreeG2R0106Witness
      fractionalNearFrameSubtreeG2R0106LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
