import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0547`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0547Mask : ℕ := 6834182851993100

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0547Witness : Array ℤ :=
  #[-1317, -2725, -1300, -1771, -1483, -345, 1027, -48, 162, 148, -196,
  1475, 2349, 1350, 1914, 2885, 911, 883, 1210, 786, 1630, 686, 1151, -83,
  825, -1241, -526, -593, -482, -1908, -613, -224, 491, 641, 539, 824, 408,
  -436, 221, 1309, -938, 498, -1200, -462, -1110, 1835, 260, 580, 2270, 730,
  718, 573, 948, 122, 687, 0, -238, 560, 1110, -1329, -235, 21, -766, -147,
  -1222, 0, 943, 0, 764, -142, 1, 770, 1276, 440, 169, 350, -190, -103,
  -1012, 1457, 1577, 17, 538, -1440, -1243, 230, 670, 877, 2784, 197, 145,
  1078, -730, -743, -86, 1612, -2111, -41, 1189, 538, 2781, 213, -125, -724,
  -1383, -1770, -345, -1937, -1294, 757, 673, 836, 2178, -510, -1332, -1444,
  -1850, 249, -134, 550, 1099, 1544, -91, 708, -2520, -621, -1067, -1024,
  345, -158, 1198, -2082, -295, -1300, -100, -3153, 2086, -483, -510, -791,
  2459, 374, 1384, 1483, 657, 1384, 255, 1140, 833, 430, -1286, 51, 774,
  -1451, 616, 1284, -945, -692, -405, -382, -605, -405, -1383, -785, -8,
  133, -1177, -703]

theorem fractionalNearFrameSubtreeG2R0547_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0547Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0547Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0547Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0547_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0547LowerBoundTable : List ℤ :=
  [-491, -1997, -2530, 1756, 900, 2044, -432, 1501, 2996, 4015, -1872, 99,
  3010, -3048, -2461, -1561, 451, 518, 3743, 2459, 5560, 1550, 6157, 5322,
  5728]

def fractionalNearFrameSubtreeG2R0547LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0547Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0547LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
