import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0011Mask : ℕ := 265908682936837

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0011Witness : Array ℤ :=
  #[-3718, -3179, -1466, -2457, -1327, -4008, -408, 1406, 3340, 2483, 0, 0,
  2662, 1408, 793, 2445, 1411, 2771, 1874, 135, -332, 831, -333, 2359, 969,
  1333, 1024, 1229, -2281, 963, -122, -1171, -1911, -870, 240, -1109, 801,
  0, -290, -673, 1555, -363, 1007, -651, 925, 1221, -28, -953, 457, 882,
  1027, 541, 36, -178, 300, -1072, 1076, 539, -707, 738, -1992, 2033, 2088,
  -636, -1905, 938, 4789, -370, -1863, -1095, 2647, 1616, 846, 2789, 2063,
  -1634, 713, 951, -448, -834, -1372, 1060, 80, 1069, 1436, 1192, -391,
  -277, 2400, 994, 1470, 1659, -539, 1688, -2272, 55, 501, 327, 431, 1050,
  301, -1399, -1311, 238, 138, 2176, 1726, -141, 1246, -278, 1452, 2065,
  1966, 203, -2722, -2499, -537, 2267, 400, -68, 168, 853, -1036, 254, 1059,
  453, 562, -464, -2022, -615, 1316, -1363, 101, -307, 886, 2367, -1756,
  1945, 495, -454, 756, 1560, -721, -37, 1565, -607, -173, 1136, 681, -2440,
  927, 926, 441, -663, -998, 1500, 879, 1514, -1262, 325, -549, -2275, 424,
  -1369, 685, 2387, -845, -233]

theorem fractionalNearFrameSubtreeG1R0011_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0011Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0011Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0011Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0011_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0011LowerBoundTable : List ℤ :=
  [1404, 1350, 1761, 5121, 4139, 33, 1788, 2940, 4413, 2059, 101, 6168,
  4542, 6999, 6160, 4932, 1625, 2079, -2522, 7984, 7646, -3005, 6614, 12358,
  866]

def fractionalNearFrameSubtreeG1R0011LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0011Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0011LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
