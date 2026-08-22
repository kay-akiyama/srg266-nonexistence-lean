import SRG266.Certificates.FractionalNearFrameSubtree.G3R0144S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G3R0144`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0144_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0144Mask fractionalNearFrameSubtreeG3R0144Witness
      fractionalNearFrameSubtreeG3R0144LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
