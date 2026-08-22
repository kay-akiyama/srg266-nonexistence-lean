import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0442`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0442Mask : ℕ := 5786357800152216

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0442Witness : Array ℤ :=
  #[599, 777, 549, -978, 81, 351, 1682, 456, 873, 388, 742, -560, -951,
  -981, 59, -619, 2464, -601, -1351, -587, 83, -602, 535, 751, -194, 2195,
  2118, 177, 0, -431, -349, 468, 69, 344, -734, 787, -167, -1306, -67, 341,
  701, 432, 75, 464, 316, 667, -191, 1510, 858, -575, -1107, -135, -261,
  2753, -1094, -1064, -1386, -826, -1298, -3443, -1592, -646, -934, -836, 0,
  -368, -838, -1509, 518, -1739, 870, 2719, -5895, -1478, 1089, 466, -1469,
  1094, -261, 266, -457, 1325, -742, -606, -188, 331, -61, 176, 558, -96,
  378, 1708, 1886, 720, 177, 314, -391, -2583, 573, 1679, -300, -1982, 538,
  1047, 1059, 1240, -1081, 701, -706, -1264, 1139, 828, -1249, -1421, 1141,
  699, 353, 1488, 568, 614, -164, 38, -501, 36, -313, -1397, 912, -532,
  -1669, -624, -2063, -2202, -1402, -2439, -3311, 2960, 908, 1509, 1312,
  1247, -1567, -77, -560, -477, 276, -231, 434, 587, -1533, 2206, -425, 107,
  117, 489, 3071, -3696, 360, -160, -1069, -2451, 736, 24, -150, -119, 1353,
  -978, -1613, -1485]

theorem fractionalNearFrameSubtreeG2R0442_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0442Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0442Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0442Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0442_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0442LowerBoundTable : List ℤ :=
  [-2909, -2654, -3784, -2107, 1698, 359, -1204, 32, -750, 100, -5908, 8062,
  1788, -967, -3193, -135, -7913, 100, -2001, -3401, 100, 34, 3892, 101,
  3400]

def fractionalNearFrameSubtreeG2R0442LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0442Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0442LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
