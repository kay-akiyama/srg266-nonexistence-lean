import SRG266.Certificates.FractionalNearFrameSubtree.G5R0068S1
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[1, 7)` for `G5R0068`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0068_t00 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0068Mask fractionalNearFrameSubtreeG5R0068Witness
      fractionalNearFrameSubtreeG5R0068LowerBoundTable 1 7 = true := by
  decide +kernel

end SRG266.Certificates
