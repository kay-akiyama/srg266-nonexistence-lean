import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0024`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0024Mask : ℕ := 5160887014344969

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0024Witness : Array ℤ :=
  #[-114, 127, 180, -831, 263, -121, 341, 283, 352, -95, 442, 621, -328,
  -442, -220, -363, 52, -540, 115, -327, -605, 259, 480, 181, -411, 186,
  -160, 299, -168, 268, 0, 612, 44, -73, 410, 0, -56, 870, 794, -630, 167,
  -117, 710, -374, -373, -128, -112, -183, 433, 8, 111, -211, -376, 124,
  -29, 347, -286, 98, -155, 663, 143, -98, -94, 477, -65, -98, 20, 350, 272,
  -221, -86, -213, 323, -76, -146, -183, -755, -269, 18, -131, 198, -52,
  875, 333, 69, 681, 343, 296, 124, 430, -44, 391, 564, 705, -526, 400, -61,
  134, -179, 585, 553, 13, 19, 75, 444, -695, -580, -371, -467, 579, -177,
  510, 453, -256, -280, -581, 118, -475, 153, -285, 143, 680, 228, 201, 0,
  -270, -82, -315, 239, -605, -278, 619, -28, -225, 188, 400, -28, 33, 104,
  -315, 86, -190, 433, 150, -91, 321, -52, 362, 422, 387, -278, -306, -65,
  168, -326, 45, 321, -652, -624, -411, -342, 276, -10, 341, -119, 302, 158,
  470]

theorem fractionalNearFrameSubtreeG4R0024_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0024Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0024Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0024Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0024_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0024LowerBoundTable : List ℤ :=
  [125, 31, 710, 32, 32, 1124, 1199, -181, 822, -197, -90, 923, -541, 1913,
  1548, 592, 99, 1009, -342, 938, 113, 2044, 2650, 100, 99]

def fractionalNearFrameSubtreeG4R0024LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0024Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0024LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
