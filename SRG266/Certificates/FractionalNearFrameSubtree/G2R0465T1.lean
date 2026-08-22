import SRG266.Certificates.FractionalNearFrameSubtree.G2R0465T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G2R0465`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0465_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0465Mask fractionalNearFrameSubtreeG2R0465Witness
      fractionalNearFrameSubtreeG2R0465LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
