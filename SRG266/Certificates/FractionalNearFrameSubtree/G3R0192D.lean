import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0192`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0192Mask : ℕ := 6866923172863512

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0192Witness : Array ℤ :=
  #[-33, -83, 22, 5, 79, -2, -1, 37, -21, 12, 26, 1, 60, 73, -13, 56, -27,
  44, 40, 43, 101, 88, 156, 20, -86, -81, 1, -96, 32, 77, 51, 35, 50, -19,
  55, -16, 21, 1, -94, -25, -71, -42, -15, -65, 30, -85, 113, 170, 86, -24,
  -79, -44, 132, 77, 90, -47, 20, 53, 112, -71, -44, 26, -58, 96, 107, -20,
  -24, -27, 29, 8, -56, 195, -212, 132, 6, -45, 13, 29, 84, 103, -5, -56,
  -40, 12, 110, -66, -26, 44, 93, 6, -134, -30, 41, 113, 0, -10, 26, 21, 37,
  -33, 44, -25, 45, 63, 2, -20, -39, -43, 43, -89, 86, -19, -61, -27, 11, 1,
  136, -32, -20, -31, 45, 54, -47, -87, -75, 63, 59, 28, -29, 22, 23, -11,
  13, 4, 45, -22, -10, -4, 12, 9, 159, -46, -16, -12, -51, 90, 141, -89, 33,
  -14, 31, 145, 0, -68, -27, -82, 18, 6, -84, 63, 88, 94, 77, 173, 1, 2,
  -35, 44]

theorem fractionalNearFrameSubtreeG3R0192_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0192Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0192Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0192Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0192_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0192LowerBoundTable : List ℤ :=
  [67, 116, 183, 240, 82, 2, 124, 71, 221, 158, 358, -42, 168, -108, 260,
  118, 387, 338, 12, 239, 76, 409, 288, 426, 210]

def fractionalNearFrameSubtreeG3R0192LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0192Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0192LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
