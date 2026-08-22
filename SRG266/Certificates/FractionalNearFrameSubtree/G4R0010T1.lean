import SRG266.Certificates.FractionalNearFrameSubtree.G4R0010T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0010_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0010Mask fractionalNearFrameSubtreeG4R0010Witness
      fractionalNearFrameSubtreeG4R0010LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
