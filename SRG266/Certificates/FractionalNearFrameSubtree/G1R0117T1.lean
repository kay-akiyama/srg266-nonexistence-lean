import SRG266.Certificates.FractionalNearFrameSubtree.G1R0117T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G1R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0117_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0117Mask fractionalNearFrameSubtreeG1R0117Witness
      fractionalNearFrameSubtreeG1R0117LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
