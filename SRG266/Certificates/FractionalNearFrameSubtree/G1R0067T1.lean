import SRG266.Certificates.FractionalNearFrameSubtree.G1R0067T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G1R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0067_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0067Mask fractionalNearFrameSubtreeG1R0067Witness
      fractionalNearFrameSubtreeG1R0067LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
