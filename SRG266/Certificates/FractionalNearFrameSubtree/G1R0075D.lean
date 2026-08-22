import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0075`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0075Mask : ℕ := 890286340942857

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0075Witness : Array ℤ :=
  #[-4664, -3830, -2214, -2310, -2642, -1500, -99, 953, 2937, 2138, 1473,
  4140, -1010, -1879, 140, 1852, 2261, 168, -362, 1326, 250, 1160, 1358,
  342, -991, 822, 1141, 585, -2473, -88, -3364, 115, -1663, 181, 311, -263,
  -969, -3182, -2382, 10, -212, 545, 2378, 4342, 564, -410, 1201, -50, 1274,
  -171, 505, 2713, 1547, 419, -822, -64, 398, 236, 0, 1156, -692, -909,
  2261, -800, 1478, 1299, 1609, -307, -264, 1127, -1775, 1147, -122, -644,
  347, 177, -259, 1030, 1598, -144, 599, -718, -2063, 1271, 548, -598, 2422,
  -1395, 484, -846, 1074, 125, 2203, -263, 545, 1168, 1084, 1129, 971, -500,
  -838, -388, 358, 1345, -232, 1264, 1781, 1209, 160, -486, 851, -256,
  -2981, 938, -1018, 4553, -864, -2397, 342, -964, 1749, -431, 1512, 2499,
  480, 121, -48, 1452, 2146, 955, -414, 832, -643, -1628, -1105, -1348,
  1558, 148, -1387, 107, -234, -1689, 1178, 3002, 1486, 41, -329, -1144,
  750, -3, -2184, 275, -21, -1994, -147, -750, -1320, -2180, 2475, 877,
  1423, -1159, -1933, -1762, 327, 1296, 2803, -2425]

theorem fractionalNearFrameSubtreeG1R0075_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0075Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0075Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0075Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0075_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0075LowerBoundTable : List ℤ :=
  [1450, -429, 4643, 1695, 31, 2155, -751, 927, -2090, 3970, 2030, 4028,
  102, 6647, 2045, 7297, 3672, 1159, 4383, 1973, 2240, 1279, 4958, 718, 100]

def fractionalNearFrameSubtreeG1R0075LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0075Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0075LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
