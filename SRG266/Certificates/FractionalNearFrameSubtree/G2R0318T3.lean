import SRG266.Certificates.FractionalNearFrameSubtree.G2R0318T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0318`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0318_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0318Mask fractionalNearFrameSubtreeG2R0318Witness
      fractionalNearFrameSubtreeG2R0318LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
