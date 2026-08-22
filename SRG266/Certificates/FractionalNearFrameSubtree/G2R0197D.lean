import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0197`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0197Mask : ℕ := 2338373084619779

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0197Witness : Array ℤ :=
  #[0, 1548, 1095, 164, -109, 244, -1185, -2483, -1081, -454, -1635, 372, 0,
  -576, -494, 1196, 752, 1669, -600, -334, -462, -129, -344, 314, 1566,
  1175, 1017, 1626, 4073, -2476, -1763, -91, 355, -4257, 718, 1316, -85,
  -822, -72, 305, -1654, -1852, 1057, 484, -67, 0, 3903, -79, 0, 473, -2427,
  568, 852, -1315, -619, 542, 1359, 2247, -791, -1299, 95, -67, 811, 555,
  1245, 1416, -774, -842, -527, -177, 11, -86, 99, 282, -80, -245, -51,
  1253, -821, 102, 801, 477, -387, -639, 1361, 9, 509, 1057, 1564, 11, -132,
  30, 619, 407, 589, -9, 826, -58, 1369, -597, 709, -606, -457, -118, -37,
  16, -62, 350, 2527, 2607, -180, 2831, 1201, -783, -859, -1879, 350, -236,
  630, 827, -44, -209, -784, -1846, -665, -562, -215, 723, 268, 594, 1058,
  1185, -74, 240, -74, -628, 220, 120, 154, -722, 718, -576, -4, -530, -431,
  317, 618, 1065, -964, -80, -838, -752, 246, -1955, -428, -470, -979, 523,
  1092, 310, -350, 576, 1317, 176, 2123, -345, 197, -2973]

theorem fractionalNearFrameSubtreeG2R0197_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0197Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0197Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0197Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0197_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0197LowerBoundTable : List ℤ :=
  [-144, 31, 3779, 1567, 1535, 31, -22, -651, 235, 995, -1492, -103, 1643,
  1785, 7417, 3876, 2940, 1051, 2066, 4057, 2292, -837, 4587, 100, -3064]

def fractionalNearFrameSubtreeG2R0197LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0197Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0197LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
