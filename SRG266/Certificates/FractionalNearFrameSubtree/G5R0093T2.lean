import SRG266.Certificates.FractionalNearFrameSubtree.G5R0093T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0093`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0093_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0093Mask fractionalNearFrameSubtreeG5R0093Witness
      fractionalNearFrameSubtreeG5R0093LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
