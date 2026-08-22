import SRG266.Certificates.FractionalNearFrameSubtree.G2R0616T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0616`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0616_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0616Mask fractionalNearFrameSubtreeG2R0616Witness
      fractionalNearFrameSubtreeG2R0616LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
