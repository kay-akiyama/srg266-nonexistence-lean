import SRG266.Certificates.FractionalNearFrameSubtree.G5R0079T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0079`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0079_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0079Mask fractionalNearFrameSubtreeG5R0079Witness
      fractionalNearFrameSubtreeG5R0079LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
