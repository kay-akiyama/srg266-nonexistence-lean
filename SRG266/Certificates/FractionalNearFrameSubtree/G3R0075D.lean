import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0075`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0075Mask : ℕ := 2355546497326097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0075Witness : Array ℤ :=
  #[0, -1716, -3592, 202, -1856, 17, -1062, 962, -2706, -1785, -3115, -1094,
  2278, 2360, 2158, 2410, -392, 5302, 1359, 2544, -845, -606, -1036, 1711,
  1004, 2295, 1046, 1374, -1356, -1505, 0, -5680, -466, -1614, -2564, -1681,
  554, 1970, 1427, 2583, -1674, -240, -1257, -742, 3611, -1345, -246, 2008,
  868, -1584, -426, -798, 981, 141, -1390, 878, -1325, -649, 1752, -240,
  -39, 101, -288, 1235, -395, 1479, 2109, 916, -30, 568, 139, 971, 368,
  1120, 217, 1308, -1294, 719, 0, 1645, 1328, 728, 18, -137, 3400, 1435,
  -1940, 287, -663, 332, 565, 933, -47, 1099, 617, 1478, 2305, -765, 289,
  649, -51, 271, 778, 4073, -2216, -453, -1183, -1583, -1705, -923, -645,
  -2843, 1614, -1458, 338, 648, -333, -314, 216, -2190, -686, -310, 2550,
  809, -1274, -446, 302, -3894, -1992, -463, 628, 8, -390, -1749, -586,
  -624, 876, 1488, -3236, -835, 1678, 310, 742, -644, 2672, -2362, 165,
  2127, -62, 2586, -3480, -2014, 2314, 1493, -1023, 1589, 1671, 2993, 407,
  -1340, -337, 2868, 2800, -1939, 2092, 1561, 0, 2795]

theorem fractionalNearFrameSubtreeG3R0075_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0075Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0075Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0075Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0075_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0075LowerBoundTable : List ℤ :=
  [-1047, 1434, 7233, 557, 1330, 1075, 2991, 31, 32, -6473, 2849, -1352,
  1393, 9122, 1411, 1868, 2547, 3213, -2546, -1648, 10168, -527, 5495, 4835,
  -3165]

def fractionalNearFrameSubtreeG3R0075LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0075Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0075LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
