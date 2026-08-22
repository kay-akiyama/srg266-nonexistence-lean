import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0100`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0100Mask : ℕ := 952003687195910

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0100Witness : Array ℤ :=
  #[-104, 23, 82, 82, 139, 141, -310, -149, -90, -47, -169, -225, -17, 81,
  -2, 98, 219, 211, -104, 39, 14, 151, 148, -146, -4, 14, -81, -122, -100,
  93, 0, 119, 28, 16, -1, 33, -62, 23, 143, 37, 60, -39, 20, 0, -66, 20, 9,
  -19, 79, -67, -21, 1, 101, 126, -56, 8, 130, 54, -86, 94, 49, 27, 33, 1,
  232, 90, 28, 5, 36, -5, -31, -36, -50, 49, 19, -62, 7, 27, -81, 65, 52,
  61, 106, -8, 60, 14, -66, 55, -67, -11, -10, 27, -85, -14, -41, -117, -19,
  36, -126, 23, -41, 117, 45, 95, 48, -115, -43, 29, 7, 30, 58, -21, -23,
  41, 66, 86, 88, 80, -13, 73, 25, 19, -97, 18, 15, -12, 18, 196, 69, 197,
  -99, 3, 51, 86, 128, 25, 62, -87, 17, -34, 75, 98, 106, 40, 40, 76, 160,
  -21, 103, 155, 175, 2, 10, 129, -15, 19, -93, -76, 60, -94, -13, 149,
  -251, 37, -79, 24, -71, 90]

theorem fractionalNearFrameSubtreeG1R0100_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0100Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0100Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0100Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0100_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0100LowerBoundTable : List ℤ :=
  [192, 394, 2, 260, 236, 207, 267, 2, 2, 779, 353, 277, 132, 353, 411, 114,
  249, 10, 228, 231, 179, 258, 106, 114, 344]

def fractionalNearFrameSubtreeG1R0100LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0100Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0100LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
