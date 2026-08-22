import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0044`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0044Mask : ℕ := 538513508077908

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0044Witness : Array ℤ :=
  #[-98, -62, -120, -27, -60, 37, 15, 32, 4, 2, 19, 84, 52, 18, -33, 10,
  -76, 6, -15, -28, 64, 52, -10, 16, -4, -18, -43, -54, -35, -82, 8, -60,
  -60, -59, 79, 90, -49, -32, -26, 88, 55, 65, 14, -28, -58, 50, 30, -37,
  -46, -25, 19, 57, 45, -84, -113, -118, -146, -13, 32, 79, 59, 125, 40, 41,
  122, 90, -78, -8, 48, 65, 3, 20, 19, 11, -25, -7, 12, -5, -59, 32, 11, 14,
  14, 41, 61, -8, -2, 53, 18, -26, -26, 7, -7, 45, -5, 3, -4, -61, 28, 19,
  44, 25, 5, 0, 79, 97, 23, -4, 33, -45, -61, -16, -78, -57, -64, 5, 86, 54,
  97, 1, 27, -23, 16, -47, -11, -5, -6, -25, -33, -74, -10, 19, -17, 17, -9,
  1, 2, -61, 26, -43, -3, 47, -3, 26, 7, -14, -66, 39, 72, 24, 15, -64, -2,
  14, -22, 43, 13, 17, 34, 42, -109, 42, 15, -27, -15, 17, 73, 63]

theorem fractionalNearFrameSubtreeG1R0044_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0044Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0044Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0044Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0044_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0044LowerBoundTable : List ℤ :=
  [-16, 2, 70, -66, 30, 56, 27, 2, -2, 150, 332, 30, -93, 306, -40, 109,
  -40, 99, 33, 3, -157, 10, 30, 26, 104]

def fractionalNearFrameSubtreeG1R0044LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0044Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0044LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
