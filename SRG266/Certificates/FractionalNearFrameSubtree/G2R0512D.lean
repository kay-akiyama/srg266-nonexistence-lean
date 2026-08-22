import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0512`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0512Mask : ℕ := 5812269353722644

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0512Witness : Array ℤ :=
  #[1456, 1057, 1523, 167, 23, 163, -160, 48, 809, 765, 871, -808, -467,
  -1123, 0, -1011, 445, -1025, -1137, -867, -1542, 732, -6, 80, 998, 704,
  299, 412, 2266, 628, 797, 500, 312, 104, -398, -645, -1562, -262, -1343,
  268, 628, -428, -1173, -554, -261, -546, -614, -346, 185, -926, 952, 343,
  -1705, 673, -1514, 1184, 626, 62, -575, -591, 804, 808, 885, -385, 173,
  1011, -1333, -1140, -977, 0, -189, 29, -349, 613, -169, 538, 1266, -1636,
  477, 1216, -305, 226, -551, 1061, -24, 959, 914, 316, -464, 609, 111,
  1125, 569, 285, 277, 1237, -33, 446, 253, 513, -474, -201, -201, -517,
  -120, 329, 1640, 769, 811, 219, 777, 342, 723, 177, 128, -483, -356, 404,
  806, 90, -443, 922, 127, 832, 26, 1894, 1, 802, 1076, 599, 993, -1046,
  139, -338, 751, 383, 1050, -346, 654, 1149, 566, -441, 782, 630, -762,
  1009, -609, -226, -90, 1244, 161, 447, -958, 1606, 87, 1757, 1278, 1088,
  -1375, 563, -61, 1930, 540, 329, 1051, 1196, 66, 279]

theorem fractionalNearFrameSubtreeG2R0512_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0512Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0512Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0512Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0512_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0512LowerBoundTable : List ℤ :=
  [1881, 4190, 2362, 2899, 1417, 400, 2561, 1966, 2933, 2602, 2446, 8787,
  4913, 4090, 1641, 5334, 286, 2091, -1479, 1176, 3822, 1460, 3491, 1462,
  99]

def fractionalNearFrameSubtreeG2R0512LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0512Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0512LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
