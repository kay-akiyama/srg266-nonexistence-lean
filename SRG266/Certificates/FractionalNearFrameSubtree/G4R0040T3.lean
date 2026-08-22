import SRG266.Certificates.FractionalNearFrameSubtree.G4R0040T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G4R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0040_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0040Mask fractionalNearFrameSubtreeG4R0040Witness
      fractionalNearFrameSubtreeG4R0040LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
