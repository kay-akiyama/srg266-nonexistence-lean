import SRG266.Certificates.FractionalNearFrameSubtree.G1R0025S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G1R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0025_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0025Mask fractionalNearFrameSubtreeG1R0025Witness
      fractionalNearFrameSubtreeG1R0025LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
