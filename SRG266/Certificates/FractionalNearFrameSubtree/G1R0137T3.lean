import SRG266.Certificates.FractionalNearFrameSubtree.G1R0137T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0137_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0137Mask fractionalNearFrameSubtreeG1R0137Witness
      fractionalNearFrameSubtreeG1R0137LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
