import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0649`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0649Mask : ℕ := 36138420590600713

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0649Witness : Array ℤ :=
  #[-778, 1292, -564, 170, 0, 236, -255, -78, 751, -561, 1107, 665, -1141,
  666, 0, 852, 0, -1444, 607, -231, 1151, 514, 217, 1121, 318, 1153, 540,
  1927, -326, -143, -1250, -963, 708, 1217, -447, -2303, -224, -597, -200,
  -894, 1016, 294, -586, 1243, -1341, -331, -1465, -2156, 28, 406, 958,
  1174, -309, 68, 187, 733, 1363, 587, 2583, 661, 86, -22, 458, -373, -772,
  -229, 769, 65, 1087, 0, 1030, 88, -145, 1257, -678, -440, -94, -154,
  -1322, -272, -127, 739, -551, -310, 378, 20, 2796, 550, 54, 124, 63, 813,
  323, 515, 510, 928, 1491, 653, 1362, 1422, 960, 2117, 1219, 1192, 1505,
  -2183, 1929, 273, 542, -385, -1330, 896, 611, 514, -503, -1407, -265, 886,
  -801, 1580, -202, -613, 1390, -788, 488, 51, -309, 1675, 223, 2367, -403,
  -305, 0, 948, 242, 665, 1168, -602, -335, 1272, 163, 2655, 325, -132,
  -467, -956, -365, 370, 187, 287, 561, 752, 282, -2016, 1156, 1867, -240,
  -1884, -2651, -214, -1302, 367, 58, -1310, -2639, 109, 546, -1241]

theorem fractionalNearFrameSubtreeG2R0649_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0649Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0649Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0649Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0649_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0649LowerBoundTable : List ℤ :=
  [2079, 34, 33, 7353, 507, 1071, 31, 4168, 32, -710, 3950, 1968, -1066,
  -1107, 2856, 1912, 1902, 7206, 6067, 4664, 1064, 614, 3520, 2241, 7261]

def fractionalNearFrameSubtreeG2R0649LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0649Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0649LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
