import SRG266.Certificates.FractionalNearFrameSubtree.G3R0166T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G3R0166`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0166_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0166Mask fractionalNearFrameSubtreeG3R0166Witness
      fractionalNearFrameSubtreeG3R0166LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
