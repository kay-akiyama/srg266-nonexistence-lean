import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0106`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0106Mask : ℕ := 5754103820658953

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0106Witness : Array ℤ :=
  #[-114, -100, -66, -177, -71, -172, -111, 52, -36, 0, -49, 144, 209, 164,
  227, 292, 195, 193, 214, 103, 170, -90, 4, 92, 186, 84, 138, -306, -294,
  -142, -237, -158, 69, -41, 56, 71, -31, -123, -98, 88, -132, -132, -21,
  44, 45, 124, 31, -168, 19, 52, -59, -117, 8, 86, -6, 118, -21, -121, 4,
  45, 20, 203, -130, 70, 18, 80, 59, 8, -17, -36, 38, -234, 50, 59, 6, 33,
  -2, 81, -38, -173, -7, 49, 138, -54, 54, 158, -4, 32, 138, -37, 133, -112,
  -95, -21, -41, 55, 104, -42, 227, -82, 0, 86, 3, -13, 117, -28, 76, 18,
  101, 30, 132, 84, 59, 6, 45, 72, -95, 43, -3, 66, 99, 63, 80, 84, 116, 15,
  128, 198, 0, -37, -24, -112, -27, -81, 202, -76, 170, -143, 135, 64, -7,
  -52, -149, -47, -88, 38, -194, 133, 86, -118, 170, 84, -84, 109, 51, -5,
  67, 16, -14, 6, -25, 149, -137, -73, 56, -185, -46, -7]

theorem fractionalNearFrameSubtreeG5R0106_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0106Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0106Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0106Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0106_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0106LowerBoundTable : List ℤ :=
  [57, 145, 3, 401, 128, 96, 219, 3, 68, 301, 294, 61, 320, 331, 353, 427,
  123, 456, -86, 393, 121, -17, 114, 100, 201]

def fractionalNearFrameSubtreeG5R0106LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0106Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0106LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
