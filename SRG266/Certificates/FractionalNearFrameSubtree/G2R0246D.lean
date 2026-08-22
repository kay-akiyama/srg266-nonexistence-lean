import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0246`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0246Mask : ℕ := 5161985451970968

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0246Witness : Array ℤ :=
  #[54, 131, 71, 85, -6, 37, -26, 33, -28, 123, 28, -94, -121, -135, 31,
  129, -38, 61, 50, -43, 40, -86, -38, -9, -67, 18, 89, -1, -50, -24, -63,
  61, 40, 81, 142, -6, -104, -40, 90, 135, 238, 339, 134, 131, 93, -71, -5,
  -73, 6, -32, 36, -81, -152, -201, -42, 30, -41, -116, -50, -14, 116, 93,
  177, 20, -18, 90, 9, 75, -70, -97, 58, -112, -103, -82, -16, -35, 22, -25,
  -160, -44, -52, -19, -87, 54, 128, -144, -84, -67, 53, -33, -34, -34, 4,
  75, 104, 119, -20, -13, -137, 21, -81, -58, 7, 160, 146, 43, 13, -1, 45,
  101, 62, 27, -153, 112, -51, -15, -104, 63, -28, -52, 37, -31, 21, 176,
  -7, -14, 7, 56, -2, -9, -38, 16, 9, -66, 45, 56, -34, 15, 66, 39, -13, 21,
  -31, -69, -100, -60, -26, -88, -65, -51, -127, 70, -7, 66, 107, 118, -27,
  25, 0, -29, 0, 111, 28, 47, 49, -41, -35, -30]

theorem fractionalNearFrameSubtreeG2R0246_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0246Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0246Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0246Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0246_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0246LowerBoundTable : List ℤ :=
  [-83, -51, 81, 33, -12, 0, -145, 211, 178, -192, 181, 186, 115, 374, -90,
  -102, 357, 149, 216, -10, 38, 9, 274, 151, 409]

def fractionalNearFrameSubtreeG2R0246LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0246Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0246LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
