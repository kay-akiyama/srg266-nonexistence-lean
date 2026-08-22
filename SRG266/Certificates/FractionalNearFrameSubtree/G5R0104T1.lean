import SRG266.Certificates.FractionalNearFrameSubtree.G5R0104T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G5R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0104_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0104Mask fractionalNearFrameSubtreeG5R0104Witness
      fractionalNearFrameSubtreeG5R0104LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
