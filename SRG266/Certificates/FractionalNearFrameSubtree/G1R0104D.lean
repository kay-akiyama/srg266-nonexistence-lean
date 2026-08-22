import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0104Mask : ℕ := 956321471727972

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0104Witness : Array ℤ :=
  #[194, -137, 103, -224, -225, 58, 218, 202, 177, 77, -49, -154, -175, -83,
  187, -83, -35, 7, 30, -86, -15, -151, -180, -254, 187, 59, 56, 154, 174,
  48, -117, -138, 155, 229, -200, -73, 44, 276, 283, -219, -219, -357, -187,
  -71, -82, -30, 26, 150, -73, 83, -29, 198, 58, 156, -39, -262, -265, 231,
  217, -35, 12, 187, 126, -50, -17, 62, 56, -176, -99, -18, -86, 74, 183,
  -81, -30, 35, -107, 52, -87, -101, -32, -1, -11, -107, 124, 221, -110,
  122, 15, -11, 56, 46, -79, 42, 37, 37, 67, 1, -50, -106, 100, 79, 61, 73,
  111, 19, 125, 73, 76, -160, -56, -28, -127, 86, 111, 62, 15, 48, 68, 39,
  -33, 67, -59, 188, 97, 12, -225, 199, 55, 88, -111, 23, -124, -231, 209,
  -13, -70, 63, 102, -11, 55, 64, 111, -29, 87, 95, 113, -31, -51, -217,
  -153, 26, -25, 39, -15, 151, 112, 24, -143, -44, -99, 207, -1, 120, -36,
  -159, 8, -51]

theorem fractionalNearFrameSubtreeG1R0104_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0104Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0104Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0104Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0104_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0104LowerBoundTable : List ℤ :=
  [-79, 3, 99, 76, 20, 2, 302, 3, 78, -159, 306, 55, 470, 152, 524, -295, 9,
  195, -89, 43, 681, 344, -434, 172, 174]

def fractionalNearFrameSubtreeG1R0104LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0104Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0104LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
