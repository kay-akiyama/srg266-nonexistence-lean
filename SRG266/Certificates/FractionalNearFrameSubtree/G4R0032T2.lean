import SRG266.Certificates.FractionalNearFrameSubtree.G4R0032T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G4R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0032_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0032Mask fractionalNearFrameSubtreeG4R0032Witness
      fractionalNearFrameSubtreeG4R0032LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
