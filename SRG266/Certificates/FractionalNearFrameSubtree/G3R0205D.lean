import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0205`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0205Mask : ℕ := 6880997407384216

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0205Witness : Array ℤ :=
  #[-62, 42, -34, -17, -94, 155, 91, 42, 0, 22, 56, 75, -29, -17, -13, -46,
  128, -87, 4, 85, 62, 49, 25, -20, -31, -32, -42, -73, 4, -25, -54, 185,
  89, 48, 7, 35, -8, 13, -54, -56, -14, 188, -47, 14, 63, 51, -23, -43, -3,
  -24, 21, -26, -44, 168, 207, 231, -126, -139, -146, -58, -60, -53, -107,
  -10, -34, -50, -130, 185, -285, -119, -41, -27, 36, 28, 11, -13, 0, 23,
  120, -31, -79, 69, -296, -99, -43, -295, 20, 18, 1, -58, 106, 128, -118,
  -42, -8, 187, 74, 51, 34, -114, 98, -81, 31, -113, 25, 114, 74, 1, 191,
  37, 225, -8, 40, -181, -197, 56, 13, 198, -14, -2, 164, 0, -25, -18, 39,
  15, -128, -43, -7, 61, 121, 39, -126, -59, -25, -21, 44, 35, 78, 51, 41,
  28, 20, 117, 65, 14, -174, -14, 12, -7, -58, -39, 6, -37, -120, -61, -17,
  -83, -6, -70, -219, 37, 122, 0, 66, -19, -109, -33]

theorem fractionalNearFrameSubtreeG3R0205_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0205Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0205Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0205Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0205_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0205LowerBoundTable : List ℤ :=
  [-181, -70, -41, -110, 1, -1, 2, 118, -122, 3, 87, 300, 472, 98, 342, 10,
  -453, -43, 15, 25, -428, 423, 282, -468, 221]

def fractionalNearFrameSubtreeG3R0205LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0205Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0205LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
