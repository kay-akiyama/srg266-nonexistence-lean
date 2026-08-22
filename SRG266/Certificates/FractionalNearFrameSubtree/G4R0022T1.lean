import SRG266.Certificates.FractionalNearFrameSubtree.G4R0022T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0022_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0022Mask fractionalNearFrameSubtreeG4R0022Witness
      fractionalNearFrameSubtreeG4R0022LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
