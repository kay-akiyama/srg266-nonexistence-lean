import SRG266.Certificates.FractionalNearFrameSubtree.G4R0020T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G4R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0020_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0020Mask fractionalNearFrameSubtreeG4R0020Witness
      fractionalNearFrameSubtreeG4R0020LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
