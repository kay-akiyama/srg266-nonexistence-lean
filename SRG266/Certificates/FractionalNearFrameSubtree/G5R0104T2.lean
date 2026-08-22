import SRG266.Certificates.FractionalNearFrameSubtree.G5R0104T1
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[13, 19)` for `G5R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0104_t02 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0104Mask fractionalNearFrameSubtreeG5R0104Witness
      fractionalNearFrameSubtreeG5R0104LowerBoundTable 13 19 = true := by
  decide +kernel

end SRG266.Certificates
