import SRG266.Certificates.FractionalNearFrameSubtree.G2R0496S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G2R0496`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0496_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0496Mask fractionalNearFrameSubtreeG2R0496Witness
      fractionalNearFrameSubtreeG2R0496LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
