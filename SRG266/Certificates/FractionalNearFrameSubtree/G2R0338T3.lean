import SRG266.Certificates.FractionalNearFrameSubtree.G2R0338T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G2R0338`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0338_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG2R0338Mask fractionalNearFrameSubtreeG2R0338Witness
      fractionalNearFrameSubtreeG2R0338LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
