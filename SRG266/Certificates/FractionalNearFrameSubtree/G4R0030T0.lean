import SRG266.Certificates.FractionalNearFrameSubtree.G4R0030S1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G4R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0030_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0030Mask fractionalNearFrameSubtreeG4R0030Witness
      fractionalNearFrameSubtreeG4R0030LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
