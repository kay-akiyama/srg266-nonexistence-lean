import SRG266.Certificates.FractionalNearFrameSubtree.G2R0114T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G2R0114`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0114_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0114Mask fractionalNearFrameSubtreeG2R0114Witness
      fractionalNearFrameSubtreeG2R0114LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
