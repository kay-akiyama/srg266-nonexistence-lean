import SRG266.Certificates.FractionalNearFrameSubtree.G5R0059T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0059_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0059Mask fractionalNearFrameSubtreeG5R0059Witness
      fractionalNearFrameSubtreeG5R0059LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
