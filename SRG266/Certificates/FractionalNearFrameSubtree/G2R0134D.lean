import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0134`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0134Mask : ℕ := 1354094375248460

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0134Witness : Array ℤ :=
  #[19, 83, 0, 328, 1223, 496, 1292, -161, -88, -527, -588, -99, -259, 469,
  -380, -1682, -834, -447, 37, -284, 647, 0, -323, -1225, -806, -1306, 1135,
  2275, 373, 1011, -2480, -2165, -2341, 547, 2326, 659, 1089, -637, 1326,
  -234, 1315, -1894, 712, -1192, -854, -719, -971, 253, 221, -1102, 365,
  -316, 876, -339, -831, 1120, -158, -1004, 345, 1320, 714, 703, -2348,
  -186, -1576, 521, -907, -253, 150, 751, 177, -499, 1434, 211, 592, 1591,
  842, -59, 85, -538, 224, 900, 1329, 1308, 470, -122, 639, -2226, 142,
  -993, -274, -499, 269, 1202, 946, 377, -409, 1575, -496, -544, 585, -2030,
  -596, -633, -299, -1016, -288, 1028, -308, 1838, 1285, 1064, -2012, -1347,
  -1306, -1432, -1139, 6, -981, 199, 507, -608, 507, 554, -563, -1665, 339,
  -983, -1295, 89, 1084, 1267, -183, -1304, 790, 569, 195, 1381, 1829,
  -2069, 1737, 385, -271, 378, 892, 628, 1896, -835, 717, -1508, -590, 769,
  -370, -934, -1545, -957, -1946, -195, -79, 695, -1548, 1155, -502, -1042,
  402, 435, 768, 214]

theorem fractionalNearFrameSubtreeG2R0134_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0134Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0134Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0134Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0134_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0134LowerBoundTable : List ℤ :=
  [-2427, -749, -1562, -107, 112, 31, 361, -923, 31, 944, -1808, 3309, 99,
  1217, -3404, -5120, -478, 5345, -244, -297, -945, 101, 12, 2447, -4992]

def fractionalNearFrameSubtreeG2R0134LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0134Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0134LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
