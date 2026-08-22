import SRG266.Certificates.FractionalNearFrameSubtree.G5R0089T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0089`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0089_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0089Mask fractionalNearFrameSubtreeG5R0089Witness
      fractionalNearFrameSubtreeG5R0089LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
