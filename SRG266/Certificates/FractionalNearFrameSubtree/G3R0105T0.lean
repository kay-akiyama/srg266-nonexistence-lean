import SRG266.Certificates.FractionalNearFrameSubtree.G3R0105S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G3R0105`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0105_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0105Mask fractionalNearFrameSubtreeG3R0105Witness
      fractionalNearFrameSubtreeG3R0105LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
