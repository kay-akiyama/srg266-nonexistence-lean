import SRG266.Certificates.FractionalNearFrameSubtree.G2R0397T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0397`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0397_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0397Mask fractionalNearFrameSubtreeG2R0397Witness
      fractionalNearFrameSubtreeG2R0397LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
