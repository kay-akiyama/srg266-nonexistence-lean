import SRG266.Certificates.FractionalNearFrameSubtree.G5R0072T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0072_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0072Mask fractionalNearFrameSubtreeG5R0072Witness
      fractionalNearFrameSubtreeG5R0072LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
