import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0050`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0050Mask : ℕ := 4880105423364357

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0050Witness : Array ℤ :=
  #[-156, 1, 37, -11, -70, 9, 27, -3, 6, 67, -78, -34, -10, -26, 0, 61, -40,
  -103, 0, -91, -17, 30, 37, 5, -20, 39, -86, 0, 64, 52, -63, 36, -114, 110,
  -43, 49, 18, 24, -31, 50, -13, -152, -37, -48, -29, -5, -53, -59, -9, 140,
  86, -9, 154, 80, 193, 38, 193, 110, -40, -185, -9, 29, -123, -86, 79, 36,
  -111, -25, 99, 84, -21, -80, -11, -41, -164, -32, -96, -84, -73, -13, -20,
  27, 43, -10, 21, 58, -78, -44, -21, 19, 98, -38, 80, 32, 66, -87, -93, 16,
  -67, -43, 95, -2, 46, 67, -29, -2, 55, -101, 13, 16, 59, -33, 101, 76, 28,
  51, -19, 17, 72, -16, -3, -4, -115, 21, 10, 20, 78, 10, 77, 53, 33, 44,
  99, -85, -47, 1, 204, -64, -103, 72, -84, -15, -164, 22, 74, 184, 62, 107,
  -17, 7, -172, -103, 65, -34, 1, 50, 14, 84, -84, -74, -126, 7, 0, 90, -88,
  -42, -53, -12]

theorem fractionalNearFrameSubtreeG5R0050_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0050Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0050Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0050Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0050_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0050LowerBoundTable : List ℤ :=
  [-100, 23, 1, -27, 2, -38, 20, 1, -162, 433, 396, -16, 10, 462, 13, 39,
  -374, -22, -64, 10, 121, 10, -301, 105, -93]

def fractionalNearFrameSubtreeG5R0050LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0050Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0050LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
