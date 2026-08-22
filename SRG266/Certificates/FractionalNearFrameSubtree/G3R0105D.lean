import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0105`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0105Mask : ℕ := 5248709432056472

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0105Witness : Array ℤ :=
  #[653, 1054, 812, -1091, -1177, -82, 1070, 1396, -1476, -1285, 2899, 3340,
  -400, 1798, 1281, 1801, 788, 732, -541, 822, 1915, 600, 1178, -186, -706,
  275, -2179, -376, 2243, -1453, -1242, 480, 1080, 2602, 2760, 2103, -1624,
  -1452, 352, -1761, 319, 2422, -855, 278, 686, -660, 2254, -63, 567, -1242,
  -891, -263, -201, -1640, 2758, 3237, 2033, -54, -451, 2050, -2367, -1857,
  650, -3279, 16, 2922, 3260, -643, 1079, -3833, -3005, 2237, -908, -1257,
  -1559, 1962, 2583, 1695, 1561, 1452, 1211, -2056, -529, 1562, -1220, 1414,
  -2197, -507, 2108, 2728, 2319, 1339, 1005, 849, 1490, -726, 1156, 371,
  872, -625, 1173, 535, 1432, 1371, -1607, -1364, 889, -1601, -1332, 0,
  2001, 962, -216, 1833, 688, 469, -894, 1895, 375, -882, -1959, 612, -415,
  3418, -3139, -2172, -810, 1921, 0, -2037, -331, -2648, 1475, 73, 1014,
  1532, 3330, -1308, 2243, 611, -2392, 1226, 1374, 2121, 2667, 1538, -484,
  2388, -396, 1548, 1975, 242, 2643, -285, 2567, -2881, 275, -1492, -425,
  3174, 2839, -1167, -1453, 1174, -509, 864, 653, 1759]

theorem fractionalNearFrameSubtreeG3R0105_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0105Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0105Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0105Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0105_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0105LowerBoundTable : List ℤ :=
  [2186, 4938, 3145, 4991, 7092, 5991, 6332, 5424, 4812, 3439, 6603, 2112,
  100, 4848, 3243, 2409, -355, 7575, 3128, 1744, 101, 5633, 6468, 4073,
  12420]

def fractionalNearFrameSubtreeG3R0105LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0105Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0105LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
