import SRG266.Certificates.FractionalNearFrameSubtree.G2R0325S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0325`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0325_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0325Mask fractionalNearFrameSubtreeG2R0325Witness
      fractionalNearFrameSubtreeG2R0325LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
