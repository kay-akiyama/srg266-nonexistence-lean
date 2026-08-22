import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0573`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0573Mask : ℕ := 6848277757510282

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0573Witness : Array ℤ :=
  #[396, -458, 272, 345, 18, 331, 175, 395, 546, -74, -743, 218, 0, -37,
  -26, 447, 553, 68, 519, 263, 772, -24, -121, -245, -808, -619, 230, 57,
  -60, 23, 585, 59, 472, -492, -57, -195, -1077, 563, 441, 7, 176, -68,
  -462, -257, -103, 31, 299, 209, 242, 550, -166, 46, -95, 755, 265, -518,
  588, -225, 259, 461, -176, 122, 439, 260, -225, 367, -543, -41, -276, -65,
  60, 486, 78, -310, 156, -9, -273, 63, -179, 492, -321, 300, 86, -696, 331,
  -494, 448, -216, 14, -133, 373, -190, 297, 522, -644, 200, -601, -317,
  -254, 544, -353, 166, -63, -712, -184, 657, 458, 659, 94, 462, -351, 162,
  538, 77, -213, 503, -313, 107, 30, 436, 278, 307, -52, 252, 501, 66, 1040,
  -255, 573, 741, 589, -236, 518, 412, 17, 47, 17, -343, -177, -151, -448,
  -55, 492, 513, 342, 549, 463, 655, 769, 68, -277, 883, -147, -496, 488,
  203, -107, -227, -297, 100, 133, -150, -73, -185, 0, -313, 228, -551]

theorem fractionalNearFrameSubtreeG2R0573_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0573Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0573Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0573Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0573_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0573LowerBoundTable : List ℤ :=
  [657, 1357, 32, 97, 286, 707, 1335, 1279, 936, 4130, 4221, 583, 1481, 981,
  1528, 1211, 1700, 440, -57, 1058, 1901, -885, 1356, 803, 1782]

def fractionalNearFrameSubtreeG2R0573LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0573Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0573LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
