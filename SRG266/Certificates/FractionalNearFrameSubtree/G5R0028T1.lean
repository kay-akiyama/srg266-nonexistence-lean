import SRG266.Certificates.FractionalNearFrameSubtree.G5R0028T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0028_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0028Mask fractionalNearFrameSubtreeG5R0028Witness
      fractionalNearFrameSubtreeG5R0028LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
