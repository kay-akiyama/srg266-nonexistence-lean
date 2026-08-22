import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0031`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0031Mask : ℕ := 853139034835971

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0031Witness : Array ℤ :=
  #[1187, 1422, 1310, 29, 19, -1371, -420, 80, -1908, -1252, -1780, -452,
  882, 0, 754, 256, -307, -573, -964, -836, -1158, -3125, -1227, -2865, 431,
  -613, 51, -263, 385, 1806, 2225, 2358, 2677, 1367, -434, 571, 1067, -1932,
  -1378, 997, 408, -62, -376, -798, -315, -254, 1636, -1047, -359, -647,
  -760, -1138, 0, 1226, 559, 747, 1109, 1144, 715, 1744, -1693, -142, -58,
  123, -868, -185, -66, 1515, -1051, -193, -6, 156, -589, 871, 542, -329,
  1066, -805, -695, 374, 539, 1265, -886, 1166, 582, 697, 824, 1232, 1049,
  381, 1067, 422, 270, -149, -917, 280, -395, -506, -111, 786, 1146, 27,
  719, 1330, -323, 1526, -127, -506, -269, 767, 376, -404, -535, -15, -181,
  -1230, -1487, 837, -739, 644, 2, -273, 1310, -179, -270, 384, -1946,
  -1184, 1723, 11, 677, 298, -675, 457, -26, 1316, 212, -385, 25, 2188,
  1375, -1079, 147, -1096, -142, -1259, -469, 2213, -684, -1255, -394,
  -1854, -510, 1525, 399, -1041, 345, -581, -1200, 590, -459, -296, 354,
  110, 98, 336, -192, 0]

theorem fractionalNearFrameSubtreeG2R0031_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0031Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0031Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0031Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0031_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0031LowerBoundTable : List ℤ :=
  [-1295, 31, -40, 31, -1790, 33, 2183, 468, 1239, 1994, 1994, 2488, -1100,
  3565, 4241, 1881, 3692, 602, 100, -364, -3218, 2309, 93, 102, 534]

def fractionalNearFrameSubtreeG2R0031LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0031Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0031LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
