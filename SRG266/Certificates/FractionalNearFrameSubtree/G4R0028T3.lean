import SRG266.Certificates.FractionalNearFrameSubtree.G4R0028T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G4R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0028_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0028Mask fractionalNearFrameSubtreeG4R0028Witness
      fractionalNearFrameSubtreeG4R0028LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
