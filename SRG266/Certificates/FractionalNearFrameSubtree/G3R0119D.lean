import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0119`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0119Mask : ℕ := 5389447591406248

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0119Witness : Array ℤ :=
  #[-20, -51, -40, -93, 41, -37, -74, -95, -52, 32, 35, 103, 0, 0, -29, -3,
  -98, -52, 77, -72, -20, -129, 16, 23, -97, -99, 33, -84, -92, -7, 50, 100,
  -12, -30, -4, 67, 0, -97, -114, 39, 36, -42, -47, 62, -65, 47, -4, 19, 13,
  76, -9, -39, -98, -18, -43, -112, 70, 44, -97, -63, 77, -9, 119, -107,
  -99, -1, 85, 148, -50, 0, 63, 74, 0, 57, 80, 19, 81, -86, -1, 19, -32, 33,
  4, -33, -35, -59, 26, -93, 3, 45, 25, 106, 66, -63, 16, 86, -38, 62, -82,
  -151, -87, 42, -7, -56, -2, 45, 95, 2, -86, -79, 36, -76, 55, -19, -25,
  91, 27, -2, 61, -16, -151, -66, 186, 105, -110, -71, 215, 25, 32, 115,
  -43, 191, -51, 21, 17, -51, 44, 55, 77, 0, -115, 17, 29, 26, 94, 34, -25,
  -22, -73, -143, -74, 26, 41, 30, -78, 55, 60, 93, 48, -106, -160, 112,
  115, 194, 37, 7, 43, 48]

theorem fractionalNearFrameSubtreeG3R0119_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0119Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0119Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0119Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0119_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0119LowerBoundTable : List ℤ :=
  [-137, 199, 2, 2, 2, -50, -148, -195, 37, -68, 446, 85, 339, 46, 520, -72,
  259, 180, -77, -284, -86, 9, -153, -62, 153]

def fractionalNearFrameSubtreeG3R0119LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0119Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0119LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
