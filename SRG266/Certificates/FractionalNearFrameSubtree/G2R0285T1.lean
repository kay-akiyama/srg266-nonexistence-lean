import SRG266.Certificates.FractionalNearFrameSubtree.G2R0285T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G2R0285`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0285_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0285Mask fractionalNearFrameSubtreeG2R0285Witness
      fractionalNearFrameSubtreeG2R0285LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
