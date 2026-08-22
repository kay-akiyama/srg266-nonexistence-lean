import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0235`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0235Mask : ℕ := 5091548254687753

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0235Witness : Array ℤ :=
  #[1130, 0, 1312, 439, -118, -217, 300, 108, 77, 1393, 2300, 1149, -2132,
  -753, -1873, -1558, -1566, -1992, 2027, -1415, -1325, -1652, -1891, 1822,
  -1697, -2097, -1888, -1085, 2436, 2691, 2034, 1810, 653, 1086, 838, 434,
  -61, -1056, -398, -524, -208, -233, -1959, -364, -1173, -62, -234, -918,
  -36, -526, 409, 386, -451, 163, -103, 981, -10, 234, 491, -784, 294, 79,
  153, -658, -713, -971, 949, 605, -761, 268, -575, 349, 592, -1293, 249,
  377, -628, -609, 336, 587, -537, -335, 626, 133, -315, -829, -305, -12,
  625, 777, -1104, -315, -1437, 1646, 1077, -2, 1288, 108, -472, 503, 1793,
  244, 477, 139, -383, 922, 606, 236, 1153, -656, -532, -390, -294, -1944,
  -520, -1013, 798, 759, -660, -994, -1046, -917, 458, 1181, -979, -40, 434,
  -1049, 335, 1837, -570, -147, -129, -195, -1119, 559, 923, 105, 250, 788,
  -1656, 161, 1001, -526, 89, 129, 61, -1187, -1416, 84, 900, 200, 246,
  -939, -1369, -792, 766, 1444, 485, 690, 223, 869, 702, -937, 900, 1413,
  106, -114]

theorem fractionalNearFrameSubtreeG2R0235_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0235Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0235Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0235Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0235_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0235LowerBoundTable : List ℤ :=
  [-757, 32, 1548, -917, 33, -78, -1355, 32, 32, -1690, 2027, 145, -1424,
  -1025, 3624, 879, 942, -2893, -3108, -458, -2409, -224, 843, 11, -244]

def fractionalNearFrameSubtreeG2R0235LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0235Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0235LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
