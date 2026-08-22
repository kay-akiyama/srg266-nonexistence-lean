import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0359`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0359Mask : ℕ := 5707472100336010

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0359Witness : Array ℤ :=
  #[-167, 2047, -291, -776, 1538, 506, 541, 857, 368, -65, -316, -933, -371,
  1249, 80, 1163, -1287, 570, 36, -1495, -29, 415, 2107, 1699, 1017, -66,
  2141, -114, 821, -188, -1493, -1122, -1718, -822, -1086, 1083, 2403,
  -2359, -797, 209, 2111, 3472, 865, 616, 276, 1683, 1698, 1615, -1702,
  -1990, 851, 1426, 1379, 2497, -2563, -2613, -2805, -950, 240, 274, -160,
  2069, 1790, 214, -1072, 1487, -1272, 1366, 1287, -1063, -1326, 1709,
  -1371, 534, 1267, 904, -806, -1661, -535, 1170, -2240, 998, -709, 821,
  1439, -719, -836, 739, 1406, -216, 1523, 99, 1357, 1105, 957, 66, 715,
  -277, 305, 312, -124, 1718, 1622, -531, 250, 1359, 1332, 515, -672, 0,
  -1560, 460, 789, 374, -738, 810, 448, -328, -1462, 476, -205, -1222, -203,
  0, 904, -414, 1416, -1129, -642, -2431, 1015, 637, -241, -1745, -1325,
  791, 783, 1098, 677, 1825, -26, -2128, 176, 1657, 713, 2236, 834, 1082,
  -474, -1359, -339, -828, 385, 356, 500, 1634, -54, 1884, 342, 688, -1045,
  -1239, 812, -537, -1696, 30, -196, 390]

theorem fractionalNearFrameSubtreeG2R0359_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0359Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0359Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0359Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0359_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0359LowerBoundTable : List ℤ :=
  [425, -1225, 30, 4164, 1770, 5776, -1351, 2614, 2977, 2657, 1064, 98,
  4423, 5597, 1393, 1000, -1253, 101, 9780, 1373, 5348, 2696, 4173, 5726,
  6539]

def fractionalNearFrameSubtreeG2R0359LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0359Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0359LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
