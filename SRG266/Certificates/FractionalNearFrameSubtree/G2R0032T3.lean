import SRG266.Certificates.FractionalNearFrameSubtree.G2R0032T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0032_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0032Mask fractionalNearFrameSubtreeG2R0032Witness
      fractionalNearFrameSubtreeG2R0032LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
