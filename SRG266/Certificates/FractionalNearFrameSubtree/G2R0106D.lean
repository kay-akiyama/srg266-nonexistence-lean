import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0106`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0106Mask : ℕ := 1283999500308561

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0106Witness : Array ℤ :=
  #[-33, -76, -65, -149, -86, -155, 36, 0, -5, 30, -37, -28, 168, 104, 96,
  118, 144, 48, 29, 96, 85, -29, -4, -83, 83, 36, 24, 133, -123, -88, -35,
  63, 8, -37, -35, -62, 10, -47, -7, 16, 46, 8, -55, 118, -29, 202, -7, 30,
  -71, 46, -129, -22, 3, 59, -46, -37, 18, 4, 29, 11, -43, -75, 49, 55, -42,
  -33, -53, -13, -21, 109, 20, -36, -1, -75, -6, -42, 23, 18, 38, 7, 46, 57,
  12, 26, 80, 2, 28, 32, -11, 97, 33, 35, 37, 17, -24, 40, -132, -56, 64,
  -9, -93, 19, -85, -23, 9, 111, 77, 100, 14, 4, -6, 172, -5, 26, -65, 181,
  0, 120, 62, -30, -82, 187, -17, -47, 109, 54, 43, 24, -6, 0, 9, -1, 87,
  -32, 95, 72, 52, -41, -4, -146, -74, -45, 54, -15, 26, 33, -84, -20, -31,
  -50, -2, 16, 3, 47, 92, 78, 0, -41, 18, 82, -119, -23, 75, -81, -57, 85,
  -41, -36]

theorem fractionalNearFrameSubtreeG2R0106_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0106Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0106Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0106Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0106_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0106LowerBoundTable : List ℤ :=
  [36, 84, -3, 192, -67, 2, 254, 1, 125, 393, 330, 3, 286, -126, 302, 4,
  208, 226, 367, 11, 264, 24, 240, 10, 30]

def fractionalNearFrameSubtreeG2R0106LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0106Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0106LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
