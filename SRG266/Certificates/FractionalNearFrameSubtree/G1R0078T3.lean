import SRG266.Certificates.FractionalNearFrameSubtree.G1R0078T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0078`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0078_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0078Mask fractionalNearFrameSubtreeG1R0078Witness
      fractionalNearFrameSubtreeG1R0078LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
