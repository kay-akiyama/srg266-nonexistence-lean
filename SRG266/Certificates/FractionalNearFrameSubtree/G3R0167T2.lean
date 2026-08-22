import SRG266.Certificates.FractionalNearFrameSubtree.G3R0167T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G3R0167`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0167_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0167Mask fractionalNearFrameSubtreeG3R0167Witness
      fractionalNearFrameSubtreeG3R0167LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
