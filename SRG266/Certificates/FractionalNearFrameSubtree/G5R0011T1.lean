import SRG266.Certificates.FractionalNearFrameSubtree.G5R0011T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0011_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0011Mask fractionalNearFrameSubtreeG5R0011Witness
      fractionalNearFrameSubtreeG5R0011LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
