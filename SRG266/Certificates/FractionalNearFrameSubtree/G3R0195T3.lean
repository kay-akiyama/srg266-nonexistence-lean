import SRG266.Certificates.FractionalNearFrameSubtree.G3R0195T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G3R0195`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0195_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0195Mask fractionalNearFrameSubtreeG3R0195Witness
      fractionalNearFrameSubtreeG3R0195LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
