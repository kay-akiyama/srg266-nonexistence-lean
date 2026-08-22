import SRG266.Certificates.FractionalNearFrameSubtree.G3R0116S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G3R0116`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0116_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0116Mask fractionalNearFrameSubtreeG3R0116Witness
      fractionalNearFrameSubtreeG3R0116LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
