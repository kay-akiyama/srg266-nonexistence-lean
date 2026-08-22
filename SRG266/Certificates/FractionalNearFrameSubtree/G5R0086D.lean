import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0086`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0086Mask : ℕ := 5472358277783884

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0086Witness : Array ℤ :=
  #[0, 172, 0, 890, 1043, 432, 1969, 1696, 1080, 1804, 1035, -2722, -1988,
  -2309, -2370, -298, -1327, -1768, -2556, -2244, -2071, -1034, -1621, 1394,
  -102, 639, -374, 3206, 2221, -356, 2726, 1329, 1036, 245, 1458, 882, 587,
  -87, -1214, 1108, -2017, 36, 268, 153, -947, -2175, -2087, -628, 1468, 79,
  -295, -2142, -693, 1816, -1222, 1000, -593, 1314, 611, -1469, 224, -888,
  2159, 832, 1887, 297, -166, 1330, -512, 1647, -1174, 2032, 1698, 1493,
  298, 935, -162, 868, 1266, 599, -2774, 1377, 1577, 393, 1034, 1256, 2215,
  -233, 2617, 529, 940, 730, -285, -1337, 1270, -137, -1290, 610, -126, 659,
  28, 1210, 1695, -105, 1115, 1180, 186, -925, -1152, -592, 534, 961, 1207,
  -228, -1324, 599, -2517, 2105, -896, -310, 413, -689, -1671, 217, 2223,
  223, 1456, -741, -1251, 856, 1831, -586, 730, 212, -468, -699, -1211,
  1695, -1749, -1396, 560, -620, 570, 351, 90, 2083, 457, 1606, -1701, 2201,
  -5, -1519, 953, 1936, -2558, 786, -560, 649, 1892, -1250, 1520, -703,
  -823, 1914, -716, -588, -2403, 539]

theorem fractionalNearFrameSubtreeG5R0086_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0086Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0086Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0086Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0086_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0086LowerBoundTable : List ℤ :=
  [410, 32, 2168, 1698, 2531, -486, 4015, -173, -1476, -684, 6307, 2429,
  1589, 486, 8062, 1655, -77, 1556, 5339, 3114, -1545, 7396, 6592, 3875,
  6813]

def fractionalNearFrameSubtreeG5R0086LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0086Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0086LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
