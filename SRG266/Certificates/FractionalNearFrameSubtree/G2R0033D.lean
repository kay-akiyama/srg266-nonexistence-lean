import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0033`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0033Mask : ℕ := 866264454501379

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0033Witness : Array ℤ :=
  #[1395, 5170, 2579, -201, 462, 0, -662, -1355, -2013, -874, -1794, 237,
  -4200, 2556, -1179, -1669, -1418, -630, -648, 863, 982, -2694, -376, 154,
  2703, -274, 3490, 367, 3755, -998, -1293, -1188, -3162, 4107, -863, 3316,
  35, -1910, -2983, -1621, 146, -902, -2367, 1481, 955, 689, 4856, -1370,
  -6197, -2436, 3590, 1791, 1216, 528, 2691, 711, -1611, -454, -2268, 217,
  -124, 766, 38, 619, -3502, 3429, -2522, -3543, -954, 304, -1383, 2672,
  -1347, 3113, -1, -1568, -4065, -1525, 1907, 2736, 3563, 2097, 2728, 1620,
  5486, 2396, 4823, 1502, 2372, 290, -881, -1611, -767, -324, -887, 1958,
  -1260, -228, 157, -2176, 2515, -391, 1198, 702, -676, 2511, -1288, 1690,
  726, 512, -771, -2473, -895, -893, -1512, 3152, 3279, 5280, -2115, 177,
  -2220, -1541, 979, -2226, 655, 647, 2119, 2043, -1620, 4667, 39, 1368,
  -618, 1339, 140, 893, -1477, 3477, -4147, 807, 2182, 780, 1145, 316, 4453,
  -496, -3725, 1231, -780, -1206, 3821, 302, -1660, 1876, -1256, 612, -968,
  985, 381, 0, 1470, -2994, -257, 931, 1191, 2414, -1243, -1811]

theorem fractionalNearFrameSubtreeG2R0033_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0033Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0033Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0033Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0033_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0033LowerBoundTable : List ℤ :=
  [313, 5951, 32, 4201, 32, 2243, 1552, 2387, 2119, 5558, 3972, 6588, 5045,
  8220, 6480, 5028, 1970, 374, 8196, -1444, 9032, 3980, 2343, 100, -2105]

def fractionalNearFrameSubtreeG2R0033LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0033Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0033LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
