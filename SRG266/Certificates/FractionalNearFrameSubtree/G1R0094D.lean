import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0094`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0094Mask : ℕ := 944243838984408

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0094Witness : Array ℤ :=
  #[-2223, 0, 3209, -5588, 1024, -2491, -1227, 160, -2593, -2731, 7065,
  2347, 5569, 11888, 3184, 1670, 213, -4020, -3276, 6145, 3240, 1400, 3154,
  4791, -1137, -7348, 34, 3884, -1299, -3234, -1645, 3814, 370, 2, -1173,
  -1219, 4517, 1340, 2543, 2322, 2005, 282, 3492, 3020, 8721, -3792, -5097,
  -5111, -153, -1301, -2879, 814, 996, 2962, -3798, -693, 2815, -2854,
  -3753, 3414, 3966, 1169, 4043, 359, -6419, -125, 5729, 1172, 3591, -4081,
  -1945, 1216, 353, 193, -428, 440, 950, 2910, -3403, 1697, 1903, -2300,
  3644, 3288, 847, 5676, 72, -817, 609, 3199, 1369, 3390, 45, 1600, 2315,
  -527, 6317, -49, -413, 1238, 963, -2769, -1971, -992, -3773, -2761, 486,
  2602, 2984, 3586, 2278, 1926, 2756, 1816, -3820, 3100, 1480, 147, 477,
  -1567, 5254, 1057, 2696, 1513, 4996, 1518, 1973, 1490, -2865, 3072, 3369,
  -500, 1885, 1258, 260, 246, -1164, -1838, -688, 3027, 3731, 1351, -2053,
  -114, -346, 3306, 2286, -2767, 687, -2019, 34, 2122, 1035, 1257, 2012,
  6247, 2084, 1546, -1215, 7888, -1746, 5347, -7002, 597, -216, -105, -675,
  -15]

theorem fractionalNearFrameSubtreeG1R0094_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0094Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0094Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0094Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0094_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0094LowerBoundTable : List ℤ :=
  [6614, 7294, 9830, 14858, 8195, 16295, 7884, -1412, 9431, 18184, 24277,
  2637, 14173, 9347, 11539, 8183, 8277, 11064, 4942, 100, 20039, 7462, 99,
  6137, 13114]

def fractionalNearFrameSubtreeG1R0094LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0094Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0094LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
