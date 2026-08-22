import SRG266.Certificates.FractionalNearFrameSubtree.G5R0074T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0074_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0074Mask fractionalNearFrameSubtreeG5R0074Witness
      fractionalNearFrameSubtreeG5R0074LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
