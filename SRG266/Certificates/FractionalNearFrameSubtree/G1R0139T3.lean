import SRG266.Certificates.FractionalNearFrameSubtree.G1R0139T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0139`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0139_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0139Mask fractionalNearFrameSubtreeG1R0139Witness
      fractionalNearFrameSubtreeG1R0139LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
