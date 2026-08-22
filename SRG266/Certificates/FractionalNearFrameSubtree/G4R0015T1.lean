import SRG266.Certificates.FractionalNearFrameSubtree.G4R0015T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G4R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0015_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG4R0015Mask fractionalNearFrameSubtreeG4R0015Witness
      fractionalNearFrameSubtreeG4R0015LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
