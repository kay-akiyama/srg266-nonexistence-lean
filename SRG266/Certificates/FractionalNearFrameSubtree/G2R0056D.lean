import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0056`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0056Mask : ℕ := 939845842993378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0056Witness : Array ℤ :=
  #[2258, -1453, 1719, -2255, -2110, -2173, 9047, 5361, 5658, 4640, 6489,
  -2525, -4534, -7161, -2999, -2624, -764, -438, -4046, -413, -1576, 3946,
  -1307, 1988, 1130, -1086, 2605, 2590, -782, -485, -230, 1217, -1011,
  -1351, -2661, -1078, -1811, 2122, 2783, -1606, -3995, 0, 1818, 4277, 3758,
  -1094, -1256, -3837, 1702, -1130, 1378, -1391, -1103, 185, 1730, 1217,
  313, -1704, -1378, -26, 367, 1072, 2778, 1912, -1574, 0, -2309, -401,
  -982, -1560, -378, 1177, -115, -551, -425, -3414, 1480, 1981, -1570, 551,
  569, 90, 867, 1133, 2585, -1612, -1575, -439, 1834, 1833, -404, 1859,
  2844, -1780, 1955, 1626, 1797, 2368, 1834, 503, -250, -738, -2631, -1111,
  1758, 2990, 1690, 6948, 622, 1254, 108, 467, -830, -4985, 2093, 70, 1693,
  1287, -1441, 3710, -11, 2800, 3183, 323, 267, -595, -521, -205, 986, 1656,
  21, -2833, -2602, 4461, 3333, -387, 2617, -305, 135, -3881, 544, -492,
  -1536, -170, -1789, -1336, -1410, -2569, -2571, -1986, -2527, 3674, -3165,
  3914, 1311, 4847, 129, -814, 2914, 4357, 1205, 756, -1918, 1321, 1664,
  -5391, 1852, 3335]

theorem fractionalNearFrameSubtreeG2R0056_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0056Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0056Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0056Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0056_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0056LowerBoundTable : List ℤ :=
  [-238, 3379, 3999, -1027, 3789, 7250, 680, 3791, 3620, 14977, 2856, 4219,
  6237, 6796, 702, 3826, 5821, 8031, 10409, -2934, 3209, -5494, -2617, 2677,
  5397]

def fractionalNearFrameSubtreeG2R0056LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0056Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0056LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
