import SRG266.Certificates.FractionalNearFrameSubtree.G1R0064T2
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Tail endpoint bounds `[19, 25)` for `G1R0064`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0064_t03 :
    compactTailEndpointBoundsAuditRange fractionalNearFrameSubtreeG1R0064Mask fractionalNearFrameSubtreeG1R0064Witness
      fractionalNearFrameSubtreeG1R0064LowerBoundTable 19 25 = true := by
  decide +kernel

end SRG266.Certificates
