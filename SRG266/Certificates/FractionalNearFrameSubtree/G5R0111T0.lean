import SRG266.Certificates.FractionalNearFrameSubtree.G5R0111S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G5R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0111_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0111Mask fractionalNearFrameSubtreeG5R0111Witness
      fractionalNearFrameSubtreeG5R0111LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
