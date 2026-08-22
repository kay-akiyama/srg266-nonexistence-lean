import SRG266.Certificates.FractionalNearFrameSubtree.G3R0142S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G3R0142`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0142_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0142Mask fractionalNearFrameSubtreeG3R0142Witness
      fractionalNearFrameSubtreeG3R0142LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
