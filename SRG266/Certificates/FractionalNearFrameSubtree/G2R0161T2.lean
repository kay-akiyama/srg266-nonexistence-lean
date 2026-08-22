import SRG266.Certificates.FractionalNearFrameSubtree.G2R0161T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G2R0161`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0161_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0161Mask fractionalNearFrameSubtreeG2R0161Witness
      fractionalNearFrameSubtreeG2R0161LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
