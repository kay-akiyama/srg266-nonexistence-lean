import SRG266.Certificates.FractionalNearFrameSubtree.G4R0001T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G4R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0001_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0001Mask fractionalNearFrameSubtreeG4R0001Witness
      fractionalNearFrameSubtreeG4R0001LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
