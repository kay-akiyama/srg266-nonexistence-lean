import SRG266.Certificates.FractionalNearFrameSubtree.G5R0137T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0137_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0137Mask fractionalNearFrameSubtreeG5R0137Witness
      fractionalNearFrameSubtreeG5R0137LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
