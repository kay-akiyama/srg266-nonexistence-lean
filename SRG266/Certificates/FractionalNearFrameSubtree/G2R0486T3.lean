import SRG266.Certificates.FractionalNearFrameSubtree.G2R0486T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0486`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0486_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0486Mask fractionalNearFrameSubtreeG2R0486Witness
      fractionalNearFrameSubtreeG2R0486LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
