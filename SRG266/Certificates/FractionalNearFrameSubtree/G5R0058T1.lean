import SRG266.Certificates.FractionalNearFrameSubtree.G5R0058T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0058_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0058Mask fractionalNearFrameSubtreeG5R0058Witness
      fractionalNearFrameSubtreeG5R0058LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
