import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0136`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0136Mask : ℕ := 1354102008648780

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0136Witness : Array ℤ :=
  #[1112, 1127, -24, 489, 40, -792, 1501, -143, -902, 209, -923, 1615, 1000,
  164, 333, -356, 998, -419, -932, -917, -875, 1375, 1284, 1320, -196,
  -1182, 562, 1157, 177, 335, 1296, 1111, 552, 1119, -1097, 500, 1374,
  -1956, -2009, -767, -2128, -927, 539, -246, -383, 561, -700, 343, 586,
  1092, 0, 1556, -320, 396, -1830, 378, -963, -716, -1452, -39, -1039, -195,
  1626, 554, -507, 647, 591, -192, 1804, 435, -357, 1566, -741, 135, -75,
  -528, 1900, -681, 323, -906, -547, 649, 1446, 1019, 1047, -394, 188, -416,
  -1028, 574, -209, -158, 409, -414, -207, -659, 39, -318, 952, 455, -840,
  1213, 657, 1115, 1063, 1138, -700, 739, 1443, -295, 96, 838, 0, -224,
  -621, -348, -1542, -1307, -225, 2248, -362, 588, -1033, 67, 69, 1202, -88,
  -971, 1243, -737, -855, -287, 1262, -339, 1309, 508, -277, 110, 1036,
  -128, -285, 175, -441, -10, -34, 665, -143, 1941, 612, 276, 882, 664, 217,
  524, -518, -52, 994, -1999, 1306, 36, -175, 564, -209, 1220, -376, 181,
  238, 557]

theorem fractionalNearFrameSubtreeG2R0136_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0136Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0136Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0136Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0136_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0136LowerBoundTable : List ℤ :=
  [-166, 2328, 32, 33, 2545, 32, 3031, 2641, 585, 3249, 5992, 2619, 101,
  5758, 6560, 2027, -5083, 2694, -2832, -955, -811, 7656, 6618, 3356, 2542]

def fractionalNearFrameSubtreeG2R0136LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0136Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0136LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
