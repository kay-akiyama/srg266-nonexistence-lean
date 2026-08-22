import SRG266.Certificates.FractionalNearFrameSubtree.G3R0125T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G3R0125`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0125_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0125Mask fractionalNearFrameSubtreeG3R0125Witness
      fractionalNearFrameSubtreeG3R0125LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
