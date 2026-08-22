import SRG266.Certificates.FractionalNearFrameSubtree.G4R0023T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0023_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0023Mask fractionalNearFrameSubtreeG4R0023Witness
      fractionalNearFrameSubtreeG4R0023LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
