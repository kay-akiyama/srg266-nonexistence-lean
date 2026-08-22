import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0066`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0066Mask : ℕ := 828781142393048

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0066Witness : Array ℤ :=
  #[44, -387, 1369, 838, 629, -355, 1204, 650, 1089, 0, 838, 198, 1455,
  -359, 1310, -1839, 1518, -432, -409, 813, 706, 1668, -1468, -397, -36,
  638, 444, -856, -235, 987, 221, 638, 1647, 2902, -700, -385, 720, 1762,
  805, -2757, -3671, 0, 264, -1265, 0, 295, -1417, 1165, -227, 1642, -131,
  378, 613, -994, 1391, 1643, 593, -784, 1569, -1746, -1654, 1350, -1398,
  -868, 872, -829, 811, 1261, -523, -141, 60, 2760, 592, -149, 1388, -970,
  -839, -1132, 245, -2383, 796, 1246, -95, 911, -167, 1309, 82, 307, 469,
  252, 801, 980, 1766, 47, 750, -1201, 310, -297, 127, -1360, -1633, -691,
  -224, 1083, -84, -409, -1540, 1476, -524, 2361, 747, -28, -131, -442, 22,
  21, 108, 747, -1571, -317, 880, -425, 235, 1172, 802, 717, 956, -292,
  -1036, 1606, 870, 222, 1422, 338, 1, -1445, 1040, 2358, 495, 294, -245,
  274, -375, 909, 1607, 231, -1457, 3023, 1991, 353, 1366, 208, 1633, 768,
  -753, -2059, -891, -1192, -1207, -1936, 177, -1324, 1295, 1003, 617, 68,
  813, 401]

theorem fractionalNearFrameSubtreeG1R0066_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0066Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0066Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0066Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0066_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0066LowerBoundTable : List ℤ :=
  [1445, 4061, -21, 2509, 32, 3090, 32, 4660, 2080, 2004, 366, 3255, 6020,
  1815, 1163, 1974, 2021, 4400, -239, 8976, 2590, 1752, 5088, 312, 8673]

def fractionalNearFrameSubtreeG1R0066LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0066Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0066LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
