import SRG266.Certificates.FractionalNearFrameSubtree.G2R0063T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G2R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0063_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0063Mask fractionalNearFrameSubtreeG2R0063Witness
      fractionalNearFrameSubtreeG2R0063LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
