import SRG266.Certificates.FractionalNearFrameSubtree.G3R0188T0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[7, 13)` for `G3R0188`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0188_t01 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG3R0188Mask fractionalNearFrameSubtreeG3R0188Witness
      fractionalNearFrameSubtreeG3R0188LowerBoundTable 7 13 = true := by
  decide +kernel

end SRG266.Certificates
