import SRG266.Certificates.FractionalNearFrameSubtree.G4R0003S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G4R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0003_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0003Mask fractionalNearFrameSubtreeG4R0003Witness
      fractionalNearFrameSubtreeG4R0003LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
