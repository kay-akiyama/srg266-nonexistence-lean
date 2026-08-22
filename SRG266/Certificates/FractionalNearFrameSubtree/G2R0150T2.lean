import SRG266.Certificates.FractionalNearFrameSubtree.G2R0150T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G2R0150`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0150_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0150Mask fractionalNearFrameSubtreeG2R0150Witness
      fractionalNearFrameSubtreeG2R0150LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
