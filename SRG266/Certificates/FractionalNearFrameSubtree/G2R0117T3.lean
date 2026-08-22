import SRG266.Certificates.FractionalNearFrameSubtree.G2R0117T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0117_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0117Mask fractionalNearFrameSubtreeG2R0117Witness
      fractionalNearFrameSubtreeG2R0117LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
