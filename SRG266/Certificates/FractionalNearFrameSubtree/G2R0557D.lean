import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0557`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0557Mask : ℕ := 6841834192680468

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0557Witness : Array ℤ :=
  #[-249, 289, 2650, 1235, 1527, -518, 335, 1216, -826, -846, -694, -414,
  378, 640, 1070, 1668, -401, -405, 455, 1126, -115, 199, 261, 896, -991,
  -670, 977, -65, 202, 379, -985, 477, 158, -1804, 2184, -117, 708, -1215,
  2386, -235, 1568, 975, -1701, 172, -307, 527, -279, -825, -161, -1015,
  136, 962, 385, -622, -927, -397, 1100, 541, 1193, 921, 436, 47, 92, -152,
  -560, 784, 0, -1386, 2642, 1732, 629, 0, -1568, 2524, 175, 756, -1678,
  1126, -1054, -412, -58, 1204, 1769, 959, 189, -355, 795, -851, 1403, 159,
  -683, 30, -1838, 571, 450, -2494, 2730, 592, 288, 910, -898, -92, 279,
  200, 419, -3000, -165, 429, -13, 645, -192, -1169, -295, 696, 1904, 2597,
  -4, 925, 158, 1164, -1659, -180, 0, -1938, 691, 1594, -1209, 75, 921,
  1603, 387, 186, 114, -234, 1650, 522, 1266, 896, -1483, 1134, 1036, -423,
  -1970, 1194, 679, -424, 451, 1463, 368, 101, -432, 105, 690, 1450, 419,
  724, 1019, -103, -444, 2425, -253, 1256, -1159, 1750, 135, 183, 656, 363]

theorem fractionalNearFrameSubtreeG2R0557_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0557Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0557Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0557Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0557_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0557LowerBoundTable : List ℤ :=
  [2099, 3953, 32, 3746, 528, 692, 3462, 1831, 5376, 8515, 4121, 4070, 1592,
  2762, 5375, 1274, 5547, 5820, -874, 5852, 7964, 2179, 1254, 2705, 5840]

def fractionalNearFrameSubtreeG2R0557LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0557Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0557LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
