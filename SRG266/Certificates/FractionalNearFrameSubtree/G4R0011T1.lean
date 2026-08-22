import SRG266.Certificates.FractionalNearFrameSubtree.G4R0011T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0011_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0011Mask fractionalNearFrameSubtreeG4R0011Witness
      fractionalNearFrameSubtreeG4R0011LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
