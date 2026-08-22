import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0424`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0424Mask : ℕ := 5778668734950924

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0424Witness : Array ℤ :=
  #[-1691, -3544, 0, -3913, -1924, 768, 2008, 1947, 752, 2161, 1285, -316,
  1228, -1526, 2253, 2019, 942, 28, 1458, 1720, 1782, -1822, -813, -2164,
  -2538, -1279, 414, -164, -143, 1276, -622, -267, -1974, 2118, 746, -210,
  -319, -411, 1468, 934, -640, -700, -1156, -1201, 328, 1496, 697, -113,
  972, -442, 1402, 1459, 706, -272, -1772, 0, 86, 1091, 753, 1752, -875,
  -121, 0, 276, -1400, -15, 2132, 929, -2106, 403, 559, 548, 1187, 1183,
  1168, -1219, -902, -1338, -103, -713, -471, 238, -166, 261, 338, -576,
  522, 120, 220, 1017, -21, 1722, 1103, 145, 1391, 156, 1159, 313, 129,
  -625, 1312, 2546, -880, 348, -1774, 294, -1638, -24, -1392, -2228, -1413,
  -754, 1367, 1821, 1975, 889, 23, -418, -65, -1132, -138, 172, 841, 1214,
  506, -563, -2671, -1221, -776, -24, 913, 642, -1240, -126, 266, 1213,
  -2688, 1965, -1069, 1548, 1280, 1223, 1219, -17, 179, -21, 430, -336, 764,
  336, 224, 1213, -345, -877, -166, 1557, -1116, -656, 82, 1107, -189, -800,
  -426, -761, 15, 56, -5, -1112]

theorem fractionalNearFrameSubtreeG2R0424_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0424Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0424Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0424Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0424_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0424LowerBoundTable : List ℤ :=
  [-556, 32, -2928, 2204, 85, 32, 3444, 31, 3734, 100, 6405, -2067, 3341,
  287, -4206, 99, -1506, 100, 2103, 380, 10605, 98, 4307, 3650, 99]

def fractionalNearFrameSubtreeG2R0424LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0424Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0424LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
