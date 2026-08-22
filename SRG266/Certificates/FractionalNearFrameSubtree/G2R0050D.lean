import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0050`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0050Mask : ℕ := 936547333374154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0050Witness : Array ℤ :=
  #[2200, 513, 800, -2087, -1627, 993, 0, 1951, 1081, 719, 1876, -2124,
  -1471, -1736, -143, -738, 267, 1573, 90, -1068, -89, -1063, 432, -1429,
  111, -906, 1395, 580, 469, -1231, -1815, -2016, -3268, -3478, -1168, 1465,
  1532, 490, 1365, 469, 1159, 4184, -432, 752, 434, -1810, -3233, 103, -411,
  -1209, 1760, 191, 2, -2003, 1731, 349, -15, -3181, 927, 1139, 676, -455,
  1064, 1636, 262, 1490, -2162, -544, 364, 1315, 270, -262, 111, 1301, 605,
  -2887, 237, 2337, -97, 1452, 2889, 1951, 787, 517, 1646, 118, 726, 664,
  1196, 1619, 1094, 2631, 1789, 39, 692, 565, -553, 790, -1144, -960, 271,
  -348, 413, 24, -1158, 1618, 1290, -203, -499, -372, 882, 161, 3687, 1002,
  1706, 639, 375, 2312, 79, -151, -2056, -573, -335, -232, 887, 53, 88, 719,
  -62, 2173, -401, -3149, 665, 1402, -441, 869, -2312, -673, -2579, -80,
  -108, -141, -2175, 1063, 357, 1376, -934, -1796, -743, 1561, 1264, 5361,
  -342, 522, -733, -269, -488, 1873, -434, -2727, 2978, 598, -594, 698,
  -1359, -1856, -1698, 3190]

theorem fractionalNearFrameSubtreeG2R0050_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0050Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0050Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0050Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0050_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0050LowerBoundTable : List ℤ :=
  [445, 32, 1281, 3396, 1896, 4020, 1962, 451, 1510, 7324, -482, 100, -201,
  -234, 99, -2509, 100, 8737, 6035, 4327, 1849, -1308, 5782, 4237, 5485]

def fractionalNearFrameSubtreeG2R0050LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0050Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0050LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
