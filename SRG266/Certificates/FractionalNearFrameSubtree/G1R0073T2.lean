import SRG266.Certificates.FractionalNearFrameSubtree.G1R0073T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G1R0073`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0073_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0073Mask fractionalNearFrameSubtreeG1R0073Witness
      fractionalNearFrameSubtreeG1R0073LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
