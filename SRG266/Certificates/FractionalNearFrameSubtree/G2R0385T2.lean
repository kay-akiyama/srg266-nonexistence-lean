import SRG266.Certificates.FractionalNearFrameSubtree.G2R0385T1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G2R0385`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0385_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0385Mask fractionalNearFrameSubtreeG2R0385Witness
      fractionalNearFrameSubtreeG2R0385LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
