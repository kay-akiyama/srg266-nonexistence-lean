import SRG266.Certificates.FractionalNearFrameSubtree.G5R0109T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0109`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0109_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0109Mask fractionalNearFrameSubtreeG5R0109Witness
      fractionalNearFrameSubtreeG5R0109LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
