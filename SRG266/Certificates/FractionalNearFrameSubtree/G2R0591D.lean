import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0591`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0591Mask : ℕ := 6863938378241554

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0591Witness : Array ℤ :=
  #[501, 2290, 1652, 733, 3174, 1197, -1690, 0, -1447, -1569, 2623, -669,
  802, 1488, 416, -1146, 466, 646, 656, 592, 656, -807, 434, 449, -2252,
  1831, 409, 310, 1229, 1356, 690, 1002, 1392, -1238, -297, 4083, -1847,
  666, 937, 2069, 187, -1540, -689, -1018, 1395, -1632, -643, 2830, 2192,
  3746, 1267, -1015, -601, -388, 446, 1300, 1331, -640, 1014, 1140, 2586,
  491, -1338, -1163, -1652, 2059, 2643, -642, -1727, -756, -1585, 132, -72,
  1313, -2327, 2059, -137, -541, 76, 736, -1494, 1946, 854, 2920, 91, -2121,
  1174, -32, -1189, -2646, 105, 1565, -1767, -812, 337, 2434, 1334, 681,
  -67, -382, 1112, 1079, 1587, -986, 571, -644, 1566, -1755, -1560, -44,
  1843, 2157, 858, 671, -1392, 355, 1276, 1793, 3126, -2319, -1706, -1474,
  2285, 279, 1480, 1465, -706, -90, 151, -1548, -393, 807, 734, -278, -781,
  -3651, 1109, 4211, -647, 1828, -998, 3255, -2159, 1220, 717, 187, 171,
  1193, -1296, 875, -928, -1504, 1025, -2454, 939, -1740, 1381, 244, 776,
  -1318, 658, -1307, -445, 691, -486, -1157, -2437, -19]

theorem fractionalNearFrameSubtreeG2R0591_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0591Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0591Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0591Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0591_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0591LowerBoundTable : List ℤ :=
  [1714, -375, -2137, 1683, 1352, 6631, 3160, 6604, 4079, 5918, 1765, 937,
  1990, 2368, 3533, 350, 6940, -1870, 8604, 2070, 2683, 996, 8190, 2657,
  10319]

def fractionalNearFrameSubtreeG2R0591LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0591Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0591LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
