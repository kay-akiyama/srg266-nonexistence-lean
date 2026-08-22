import SRG266.Certificates.FractionalNearFrameSubtree.G3R0120T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G3R0120`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0120_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0120Mask fractionalNearFrameSubtreeG3R0120Witness
      fractionalNearFrameSubtreeG3R0120LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
