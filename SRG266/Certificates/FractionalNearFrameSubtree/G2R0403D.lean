import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0403`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0403Mask : ℕ := 5741416058538664

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0403Witness : Array ℤ :=
  #[956, 552, -924, 330, 837, 544, 168, -687, -814, 264, 912, -151, -750,
  -686, 882, 878, -733, 1177, 357, -1205, -1216, -1294, 540, -100, -446,
  -153, 504, -404, -1166, -55, 110, -204, 896, 1128, 575, -1042, -575,
  -1565, 1091, 1103, -1420, 366, -156, 662, 858, -783, 0, 270, 406, -896,
  638, -189, -1571, -1615, 383, 701, 1005, 787, 676, 765, 611, 1631, 328,
  768, 1001, 1861, 377, 407, -126, 469, -485, 335, 909, -321, 1963, -1267,
  62, -1279, 485, 758, -383, 1295, 666, 1073, -1360, 460, 205, 159, 210,
  707, 361, -1112, 1066, 602, -78, 808, 187, 287, -439, 352, -506, 248, 705,
  857, 348, -855, -1333, -17, 1425, 7, -246, -380, 162, -675, -1017, -1630,
  -1742, -44, 62, 22, -1882, 2797, 242, 159, -850, -1490, -73, 521, -113,
  1195, 6, 239, 477, -574, 85, 324, -1030, 175, 1137, -118, -108, 115, 190,
  1156, 620, -511, -92, 483, 220, -830, -609, -268, 0, -1550, -361, -177,
  789, -21, -512, -51, -1299, -1589, -113, -7, 256, 554, -147, -41]

theorem fractionalNearFrameSubtreeG2R0403_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0403Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0403Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0403Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0403_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0403LowerBoundTable : List ℤ :=
  [-540, -1389, 700, 17, 608, 1160, 840, 32, 1629, -1683, 602, -837, 752,
  2069, 6500, -1667, -3367, 1585, 1801, -2935, -202, 2814, 2991, 2825, 2503]

def fractionalNearFrameSubtreeG2R0403LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0403Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0403LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
