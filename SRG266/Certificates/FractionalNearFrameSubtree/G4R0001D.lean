import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0001Mask : ℕ := 521900574867523

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0001Witness : Array ℤ :=
  #[-8, -20, -43, -47, -21, -25, -10, 11, -32, -73, 0, -1, 120, -76, 0, -63,
  -2, 1, -18, -7, 78, -42, 70, 29, -93, 52, 59, 70, 17, -49, -126, 16, 57,
  36, -23, 90, 97, 52, -173, -28, 46, 60, -153, 92, 30, -47, -98, 7, -115,
  -66, 118, 60, 122, 16, 115, -35, -92, 14, -88, 85, -7, -6, 98, 62, -11,
  -63, -234, -68, 167, 108, -78, 156, 106, 137, 138, -30, -36, 149, 88,
  -108, 153, -50, -47, 78, 151, 147, 49, -15, -61, -137, 136, 26, -84, -1,
  1, 173, 110, 41, -117, 114, -47, -45, -55, 147, 87, -34, 133, 98, 149,
  -218, -80, 0, -37, 14, -13, -3, -95, -121, -29, -194, -163, 81, 59, -52,
  24, -74, -73, 100, -17, -18, -85, -24, 9, 112, -75, -139, -3, 70, 51, 41,
  98, 97, -44, 118, 59, 110, 67, 22, 83, 110, -2, -11, 89, 21, -142, -49,
  12, -16, 47, -99, -97, 18, 114, 71, -59, 45, 28, -30]

theorem fractionalNearFrameSubtreeG4R0001_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0001Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0001Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0001Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0001_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0001LowerBoundTable : List ℤ :=
  [-25, 100, 83, 2, 2, 266, 100, 1, 56, 231, 136, 9, 10, 463, 284, 274, 68,
  -39, 192, 165, -173, -3, 416, 380, 9]

def fractionalNearFrameSubtreeG4R0001LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0001Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0001LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
