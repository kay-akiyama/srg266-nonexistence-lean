import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0344`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0344Mask : ℕ := 5668762935536649

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0344Witness : Array ℤ :=
  #[426, -439, 1424, -86, 730, 851, 576, -2751, 598, -1580, 0, -311, -370,
  1987, 2158, 0, -1115, -1771, 565, -1384, -1716, -2365, -677, -1160, -2538,
  -1707, -1601, -1067, 1876, 3808, 2876, 3390, 540, -1135, 128, -838, -950,
  911, 3547, 1520, -428, -949, -239, -1753, 961, 2582, 2418, -1406, 715,
  -35, 569, -1236, -1611, -1071, -554, 1601, 425, 587, 1949, 1318, 115,
  -1073, -803, 2453, -258, -2432, -1767, 1665, 0, -406, 2062, 2810, -1625,
  1366, -1357, -1664, -51, -1191, 2190, -1995, 1343, -1147, 1015, -1069,
  1273, -148, 911, 2789, 641, -1909, 1548, -344, -947, -853, 1749, -1333,
  -968, 346, 1040, -993, -2175, -1063, -1291, -884, 1285, 352, -1085, -903,
  748, -2248, 870, 1841, 598, -290, 328, -588, 2803, 1640, -313, -372, -532,
  -462, 599, 1137, 409, 269, -2078, -2144, 2587, 67, 1352, 1036, 4606, 3373,
  -192, -407, 1424, 1155, 883, -2253, 270, 980, 1809, 1426, 1603, 395, 1691,
  2506, -341, -2075, 2688, 2171, 1064, 2226, 812, -1163, 2651, -1749, -201,
  -852, -58, -192, -843, -1502, 975, 447, 208, 154]

theorem fractionalNearFrameSubtreeG2R0344_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0344Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0344Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0344Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0344_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0344LowerBoundTable : List ℤ :=
  [1576, 3061, 1207, 32, 1914, 364, 3660, 4014, 1833, 13542, 12918, 8150,
  1759, 1425, 3874, -1510, 1468, -130, -6125, -6946, 1618, 3877, 4357, 99,
  8273]

def fractionalNearFrameSubtreeG2R0344LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0344Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0344LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
