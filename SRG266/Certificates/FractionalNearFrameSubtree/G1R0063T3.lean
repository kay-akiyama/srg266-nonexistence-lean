import SRG266.Certificates.FractionalNearFrameSubtree.G1R0063T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0063_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0063Mask fractionalNearFrameSubtreeG1R0063Witness
      fractionalNearFrameSubtreeG1R0063LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
