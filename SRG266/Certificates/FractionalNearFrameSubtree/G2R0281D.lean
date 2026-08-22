import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0281`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0281Mask : ℕ := 5372939280624296

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0281Witness : Array ℤ :=
  #[-280, 611, 712, 1801, 2205, 1315, 1395, 4050, 447, -1620, -294, -2024,
  -426, -1423, 602, 156, 0, 210, -1072, 2762, 1911, 1755, 2255, 1590, -643,
  -773, -719, 918, 734, 903, 3682, -1049, -1006, 965, 303, 722, -438, 1304,
  -554, 2061, -533, 1804, 65, -999, 1383, 1356, -98, 622, 687, -201, 295,
  700, -520, 2856, -1102, 828, -172, 4145, 824, -859, -2407, 121, 280, 274,
  3637, 1190, -226, -713, 2213, 164, -1395, 2351, 2575, -1321, -761, 549,
  -1782, 741, 2881, 774, -916, 2395, -22, 409, 389, -1647, 1193, 1066, 382,
  -927, 711, 1775, 2523, 1058, 1245, 152, -820, -295, -473, 810, -125, -189,
  -86, -97, 963, -2168, -2808, 1832, -67, -1460, 568, -348, 399, -916,
  -1080, -688, 2028, -1040, -1310, 297, -1244, -402, 2132, 15, 993, -1483,
  -1320, -488, 653, 160, 1428, 890, -1519, -102, -712, -1080, -1829, -1600,
  -378, 953, -2746, 2420, -776, -488, -612, 1962, 1533, 1317, -551, 168,
  2240, 3420, 919, 461, 1325, -979, 342, 1530, -1746, 976, -1069, 1534,
  1335, 2820, 1320, 173, -959, 1469]

theorem fractionalNearFrameSubtreeG2R0281_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0281Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0281Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0281Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0281_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0281LowerBoundTable : List ℤ :=
  [3322, 2200, 5516, 7118, 1452, 933, 3359, 3093, 4595, 2743, 3064, 4579,
  2456, 5185, 1768, 5857, 6541, 100, 8344, 12763, 11235, 4265, 1998, 4638,
  7438]

def fractionalNearFrameSubtreeG2R0281LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0281Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0281LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
