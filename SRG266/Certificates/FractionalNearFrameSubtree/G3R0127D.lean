import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0127`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0127Mask : ℕ := 5402571134177896

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0127Witness : Array ℤ :=
  #[483, -1537, 576, 38, -1111, 2220, -14, 1633, 558, -227, 410, -455, 1338,
  -444, 1085, -1053, 247, 147, 500, 939, -95, 426, 846, -46, 752, -696, 148,
  1559, 1218, -344, 1495, 450, 606, 298, -1125, -501, -1352, -70, 1383,
  1837, -1054, -3881, -334, 617, -249, -1551, 1061, 527, 229, 876, -1288,
  566, 1735, 1058, -156, -151, -701, 1510, 820, -172, 312, 540, -309, 674,
  159, -2198, 326, 72, 360, -1465, 289, 131, 964, -1104, 552, 0, 743, -5,
  1246, 460, -1175, 269, -84, -632, 1104, 390, 931, -527, 522, 743, -267,
  971, -606, -71, 1339, -793, 118, 402, 2006, 824, 2463, -130, -618, 1664,
  -17, 1023, 466, -976, -1043, -559, -132, 1304, -694, 1395, -43, 712, -110,
  -32, 128, 793, 135, -219, 183, 454, 307, -1042, 1649, 820, 1284, 150, 612,
  -890, 287, -928, -673, -229, -55, 17, 248, 1132, 997, 788, -737, 966,
  2086, 246, 546, -1138, 1887, 1417, 116, 454, 814, -2278, 0, -1240, -1407,
  -347, 0, 1271, 282, 1146, -43, 1493, -204, -692, -2757, -494]

theorem fractionalNearFrameSubtreeG3R0127_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0127Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0127Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0127Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0127_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0127LowerBoundTable : List ℤ :=
  [1232, 1627, -81, 2471, 1250, 1360, 2719, 4167, 2016, 2850, 3988, 3895,
  4081, 1952, 3767, 2774, -620, 1758, 1951, 4168, 6320, -2033, 1911, 2258,
  5665]

def fractionalNearFrameSubtreeG3R0127LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0127Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0127LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
