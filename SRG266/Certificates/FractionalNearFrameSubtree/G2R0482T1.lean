import SRG266.Certificates.FractionalNearFrameSubtree.G2R0482T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G2R0482`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0482_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0482Mask fractionalNearFrameSubtreeG2R0482Witness
      fractionalNearFrameSubtreeG2R0482LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
