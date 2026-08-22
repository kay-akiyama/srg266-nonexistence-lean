import SRG266.Certificates.FractionalNearFrameSubtree.G1R0085T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G1R0085`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0085_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0085Mask fractionalNearFrameSubtreeG1R0085Witness
      fractionalNearFrameSubtreeG1R0085LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
