import SRG266.Certificates.FractionalNearFrameSubtree.G4R0019T0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0019_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0019Mask fractionalNearFrameSubtreeG4R0019Witness
      fractionalNearFrameSubtreeG4R0019LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
