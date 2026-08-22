import SRG266.Certificates.FractionalNearFrameSubtree.G5R0128T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0128`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0128_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0128Mask fractionalNearFrameSubtreeG5R0128Witness
      fractionalNearFrameSubtreeG5R0128LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
