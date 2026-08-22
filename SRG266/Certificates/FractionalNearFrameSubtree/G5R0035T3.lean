import SRG266.Certificates.FractionalNearFrameSubtree.G5R0035T2
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G5R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0035_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG5R0035Mask fractionalNearFrameSubtreeG5R0035Witness
      fractionalNearFrameSubtreeG5R0035LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
