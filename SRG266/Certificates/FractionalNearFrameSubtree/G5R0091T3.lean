import SRG266.Certificates.FractionalNearFrameSubtree.G5R0091T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0091`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0091_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0091Mask fractionalNearFrameSubtreeG5R0091Witness
      fractionalNearFrameSubtreeG5R0091LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
