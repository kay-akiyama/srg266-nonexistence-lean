import SRG266.Certificates.FractionalNearFrameSubtree.G1R0057T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0057`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0057_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0057Mask fractionalNearFrameSubtreeG1R0057Witness
      fractionalNearFrameSubtreeG1R0057LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
