import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0428`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0428Mask : ℕ := 5784240517256714

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0428Witness : Array ℤ :=
  #[1951, 1460, 1785, 1674, 1328, 5, -468, 1866, -209, -379, -1481, -350,
  915, 1294, 1650, -630, 1265, -1208, 155, -1722, -387, 325, 2914, 555, 69,
  953, 1340, 2244, 563, 803, 1473, 2149, 574, 173, 1199, -783, 2304, 630,
  -955, -1333, -2052, 1594, -957, 455, 1478, 3408, 1503, -1343, 694, 1085,
  1967, -1105, -630, -1765, 1179, -1209, 349, 3292, -21, 155, -655, -340,
  -147, 1913, 2812, 2478, 2094, 299, -1616, 351, -1938, -636, -482, 2007,
  -1454, -13, 1032, 1481, -759, 1679, -569, -3781, 1705, 1265, -756, 757,
  184, 328, 908, 86, 2312, -955, -690, -106, 803, -229, 19, 454, 2012, 674,
  -1337, -362, 463, -3007, 407, 58, -981, 1185, 2407, -240, 578, -3393, 653,
  -1101, 657, 409, 1309, -628, -1491, -3347, -1157, -2170, -1446, -1847,
  2132, 675, 1924, 1942, 1401, 1181, 1742, 1480, 1744, 778, -279, 1234, 0,
  320, -215, 1225, 2171, 377, 3286, 1507, 494, -542, -116, 738, 1052, -1312,
  1398, -127, -674, 631, -454, 340, 111, 344, -1011, 932, -1425, -341, 962,
  -90, -1422, 1121, 1629, 1851]

theorem fractionalNearFrameSubtreeG2R0428_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0428Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0428Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0428Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0428_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0428LowerBoundTable : List ℤ :=
  [2286, 2331, 2478, 4695, 2472, 5935, 3534, 4446, 6950, 7013, -427, 9787,
  100, 2435, 2925, -3504, 8039, 99, 9106, 3218, 7925, 10784, 4640, 4305,
  6674]

def fractionalNearFrameSubtreeG2R0428LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0428Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0428LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
