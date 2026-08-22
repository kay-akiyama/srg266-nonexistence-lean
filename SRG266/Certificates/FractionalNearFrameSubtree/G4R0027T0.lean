import SRG266.Certificates.FractionalNearFrameSubtree.G4R0027S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G4R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0027_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0027Mask fractionalNearFrameSubtreeG4R0027Witness
      fractionalNearFrameSubtreeG4R0027LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
