import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0130`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0130Mask : ℕ := 5403671448957360

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0130Witness : Array ℤ :=
  #[-1065, -107, -1805, 677, -646, -773, 1111, 774, 1081, 1986, 597, 1202,
  639, 683, 341, -664, -20, 717, 1032, 496, 777, 2299, 1533, 2221, -2064,
  -2875, -2561, 501, -1428, -317, 646, 465, 840, 292, -332, 809, -2345,
  -670, -832, 1533, 967, -1686, 869, 846, 1359, -384, -2259, -2738, 1084,
  1050, 1517, 235, 941, 163, -1384, -1195, 1433, -125, 1275, -264, -301,
  528, 2271, -107, 489, -138, -1035, 798, 149, -497, -121, 141, -662, 23,
  -413, 1643, -1134, -241, 127, -505, -194, 192, 297, -1110, 1514, -1903,
  -51, 2150, 1703, -438, 631, 1921, -2126, 2805, -2997, -2093, 1560, -2119,
  227, -139, 481, 1291, 1265, -1084, -295, -67, 268, -718, -1173, -346, 621,
  1950, 283, 19, 1101, 579, 590, 657, 1462, -141, 622, -900, 2483, 1552,
  -74, -835, -2989, -1871, 1942, -542, 445, 489, 774, 421, 1235, -197,
  -1184, -252, -1104, 1124, 613, -268, 1810, 83, -495, -917, 1244, -1339,
  1279, 146, -714, -293, -62, -1538, -306, 838, 0, -635, -1128, 1082, 905,
  3569, 1981, 650, 1925, 1271, -2342, -2171]

theorem fractionalNearFrameSubtreeG3R0130_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0130Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0130Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0130Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0130_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0130LowerBoundTable : List ℤ :=
  [-658, 2527, 413, 1724, -296, 2962, 2214, 34, 149, 6572, 3440, 2280, 257,
  5053, 99, -588, 1624, 3436, 730, 5392, 99, 1217, 6638, 100, 100]

def fractionalNearFrameSubtreeG3R0130LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0130Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0130LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
