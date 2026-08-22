import SRG266.Certificates.FractionalNearFrameSubtree.G1R0083T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G1R0083`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0083_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0083Mask fractionalNearFrameSubtreeG1R0083Witness
      fractionalNearFrameSubtreeG1R0083LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
