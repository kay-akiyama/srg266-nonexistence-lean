import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0409`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0409Mask : ℕ := 5742494634903920

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0409Witness : Array ℤ :=
  #[-389, 497, 1267, 38, -1343, 154, 745, -214, 85, -1592, 1702, 2153, 1079,
  818, 1370, 1616, 2265, 1312, 389, 874, 275, -477, -201, 1347, -462, -432,
  -1180, -2080, -1200, -50, -450, -235, 0, -1245, 0, 747, 558, -1772, 125,
  997, 16, 1042, 373, -275, -55, 1218, -584, -551, 384, 362, -291, 1380,
  1870, -2593, -1321, -1574, -353, 1063, -2368, 363, 446, 475, -876, 117,
  368, -254, -1612, 1137, -994, -760, -715, 1252, 608, 694, 263, 1332, 11,
  -86, -1030, -907, 279, 777, 1548, 951, 1212, -801, 1316, 196, 1426, 2287,
  1612, 363, -712, 905, 1326, 546, 666, -784, 139, 231, -125, -554, 1298,
  288, 1095, 735, -109, 833, 1226, -175, 13, 230, 58, 678, -82, 2135, -36,
  0, 549, 373, 1569, -812, -2280, -1322, -281, 58, -1360, 622, 1021, 1375,
  746, -877, 591, -1075, 309, -142, -295, 1142, 1522, 752, 2811, -620, -252,
  -1387, 650, 1239, -2357, -353, -1573, 1842, 611, 1565, 761, -1429, 1485,
  -199, 270, 1258, -907, -810, 165, 1360, 777, -143, 254, -184, 774, 679]

theorem fractionalNearFrameSubtreeG2R0409_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0409Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0409Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0409Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0409_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0409LowerBoundTable : List ℤ :=
  [1522, 2662, 2077, 4226, 5328, 3108, 773, 32, 765, 2404, 1563, 577, 1310,
  2690, 4765, 469, 101, 7374, 2330, 3536, 3520, 3375, 6470, 1975, 1008]

def fractionalNearFrameSubtreeG2R0409LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0409Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0409LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
