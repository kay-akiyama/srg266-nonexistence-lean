import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0052`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0052Mask : ℕ := 4949366215131205

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0052Witness : Array ℤ :=
  #[-990, -803, 1467, 523, 327, 4166, -855, -1239, 0, -174, -1021, -1392,
  -462, -202, 1934, 1044, -2072, 0, 546, 2359, 3853, 1777, 851, -254, 829,
  2107, -1161, -1001, 190, -1268, 392, 16, -355, -1776, -166, 1821, 3265,
  1178, 813, -2852, 0, -1441, 1069, 612, 1626, -1303, -1075, -1762, -5138,
  -1239, 2363, -909, 3646, 970, 1180, 112, 2205, 118, -904, 1417, 1430,
  2002, 2516, 1843, 596, 1882, -340, -701, 1301, 2788, -1299, 2012, 2724,
  790, 2743, 876, 2324, 645, 695, -830, 1204, 1235, -1050, 604, 1247, -313,
  1364, -237, 2148, 42, 2557, -350, 2658, -431, -818, 573, -162, -1882,
  2083, -1922, 307, -1497, 0, 256, -3267, -1507, -3525, 1002, -1836, -690,
  -1419, -108, 2318, -547, -214, 1060, -668, -1486, 1071, -1573, 62, -2051,
  749, 2875, -533, -1468, -1208, 1776, 466, 2494, -3507, -737, -204, 609,
  2036, 0, 1828, 1078, -1821, -1423, 879, 1352, -437, 221, 238, 4, 2983,
  676, 587, 1006, 76, 2232, -1476, -143, -625, 2981, -76, -347, -616, -1781,
  1386, 1429, 1500, 80, -688, 1139, -2363, 991]

theorem fractionalNearFrameSubtreeG5R0052_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0052Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0052Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0052Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0052_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0052LowerBoundTable : List ℤ :=
  [1697, 1965, 33, 5484, 2880, 2483, 2373, 4151, 3494, 3563, 2517, 1364,
  5376, 3741, 4352, 5645, 4994, 6431, -1115, 9620, 100, 4074, 5962, 7118,
  1383]

def fractionalNearFrameSubtreeG5R0052LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0052Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0052LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
