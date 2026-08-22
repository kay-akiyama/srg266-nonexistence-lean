import SRG266.Certificates.FractionalNearFrameSubtree.G1R0080T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G1R0080`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0080_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0080Mask fractionalNearFrameSubtreeG1R0080Witness
      fractionalNearFrameSubtreeG1R0080LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
