import SRG266.Certificates.FractionalNearFrameSubtree.G2R0609T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0609`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0609_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0609Mask fractionalNearFrameSubtreeG2R0609Witness
      fractionalNearFrameSubtreeG2R0609LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
