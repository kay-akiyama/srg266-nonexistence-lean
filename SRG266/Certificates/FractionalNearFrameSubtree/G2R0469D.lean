import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0469`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0469Mask : ℕ := 5809352272941652

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0469Witness : Array ℤ :=
  #[-167, -65, -26, -125, -138, 6, 74, 96, 45, 120, 105, 16, -27, 25, 0, 50,
  32, 32, 48, 36, 7, -31, -101, 31, -81, -67, -9, -78, 14, -14, -54, -38, 1,
  -24, -12, 159, 16, 40, 177, -18, -42, 82, 26, 17, 93, 45, 116, 36, -28,
  118, -89, 8, -130, -155, 55, 20, 103, 29, -60, 36, 41, 110, 157, -130,
  -144, -23, 30, 126, -17, -29, -62, -94, -68, 70, 96, 55, -58, 75, 98, -31,
  40, -91, -9, 11, -97, -88, -33, 20, -44, -28, -62, 50, -22, 58, 15, -7,
  -11, -56, 31, -71, 68, -32, 155, 71, 76, -65, 1, -41, -52, -17, -23, -15,
  -29, 58, 89, 3, -44, -90, -60, 4, 119, 60, -78, 24, 12, -24, 8, 22, -35,
  -35, 25, 50, -41, -29, 56, -1, -44, 49, -130, 61, -88, 29, 268, -85, -73,
  62, -96, 70, -191, -1, -56, -70, -12, 86, 51, 50, 3, -59, -78, 15, 87,
  -15, -11, -33, -17, -38, -40, -10]

theorem fractionalNearFrameSubtreeG2R0469_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0469Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0469Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0469Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0469_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0469LowerBoundTable : List ℤ :=
  [-96, 2, -10, -92, -95, -44, 56, 2, 11, 167, -112, 98, -127, 243, 9, -360,
  397, -333, 32, 105, 326, 84, 10, 195, 333]

def fractionalNearFrameSubtreeG2R0469LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0469Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0469LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
