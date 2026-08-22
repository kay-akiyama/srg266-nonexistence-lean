import SRG266.Certificates.FractionalNearFrameSubtree.G3R0049T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G3R0049`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0049_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0049Mask fractionalNearFrameSubtreeG3R0049Witness
      fractionalNearFrameSubtreeG3R0049LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
