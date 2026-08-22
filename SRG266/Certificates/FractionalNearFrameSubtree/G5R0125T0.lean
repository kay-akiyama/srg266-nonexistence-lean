import SRG266.Certificates.FractionalNearFrameSubtree.G5R0125S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G5R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0125_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0125Mask fractionalNearFrameSubtreeG5R0125Witness
      fractionalNearFrameSubtreeG5R0125LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
