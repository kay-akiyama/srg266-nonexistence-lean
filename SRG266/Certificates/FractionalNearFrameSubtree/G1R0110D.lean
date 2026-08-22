import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0110`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0110Mask : ℕ := 964018040310128

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0110Witness : Array ℤ :=
  #[-495, 336, 293, 271, -428, 0, 1109, -176, -915, -615, -39, 635, 967,
  961, 87, 344, 857, 419, 541, -168, 1201, -230, -1008, -1551, 173, 1338,
  386, 400, -12, 1241, 1195, -434, -855, -548, 161, 191, -1104, 491, -394,
  287, 0, -497, 476, 1681, -1172, 1053, 259, -353, 348, 255, -40, -80, -445,
  -896, 1096, 18, -149, 187, 545, -1162, -1132, 231, 491, -1865, 621, -1337,
  2020, 1227, -623, 244, -870, 121, 347, 978, 2816, 1071, -739, 1453, -1208,
  -1136, -938, -2779, 524, -1132, -810, -593, 150, 1073, 493, 1102, -1111,
  -1658, 315, -26, -831, 1185, 964, 1438, 316, 175, 614, 789, -756, 520,
  866, -1954, -2013, -911, -836, -928, 957, 1370, 126, 888, -350, -523,
  -260, -557, -833, -139, 1170, -1025, -158, -586, -516, 38, 126, 437, -352,
  -98, -462, -738, 405, 1236, 349, -48, -850, 660, 697, -601, -549, -1188,
  486, 296, 1408, 1130, -141, 317, 656, 514, 2470, -171, 795, -207, 756,
  -302, -975, 352, -158, -285, 64, -464, 0, -441, -10, 369, 1091, 360]

theorem fractionalNearFrameSubtreeG1R0110_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0110Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0110Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0110Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0110_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0110LowerBoundTable : List ℤ :=
  [-179, 1604, -1081, 32, 2700, 32, -1398, 851, 31, 1420, 1569, -1556,
  -1480, -719, -3422, 843, 848, 5908, 1911, 1356, 99, 1678, 4613, 6178,
  1130]

def fractionalNearFrameSubtreeG1R0110LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0110Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0110LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
