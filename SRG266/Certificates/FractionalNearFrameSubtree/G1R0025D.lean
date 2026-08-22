import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0025Mask : ℕ := 468080318329861

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0025Witness : Array ℤ :=
  #[-1883, 875, -591, -490, -631, -1452, 0, 62, -128, 802, -491, 0, 1792,
  1956, 668, 1251, 814, 669, -589, 596, 1477, -101, -196, -630, 1472, 1158,
  846, 1053, -515, -1865, -894, 1500, -1112, 1323, 435, -313, -1694, 2168,
  514, 9, 886, 1463, -13, -600, 1357, -1442, -3114, 1854, 635, 1631, 2258,
  1604, -743, 1136, 1688, 1137, 1747, 844, 601, -459, -1189, 339, 624, -642,
  151, 1481, -307, -1442, 411, -1795, 243, 444, 1198, 222, 6, 456, -48, 638,
  -477, -411, -1694, 582, -57, 268, 1263, 455, 400, -1086, 1224, 1616, 1234,
  -12, -493, -518, 240, 719, 152, -48, 806, -525, -833, 2526, 919, 1044,
  368, 1018, 132, 412, 1039, 536, 228, 981, 967, 1486, 1937, 393, 724, 614,
  -284, 13, 1992, 30, 2105, 1799, -309, -557, 2280, -203, -383, -1410,
  -1009, 1295, 1642, 569, 11, 972, -38, -860, -568, 912, 5, -32, -774, 700,
  -30, 674, -140, -17, -639, -1085, -110, 567, 351, -525, 719, 2587, 2439,
  475, -739, -544, 275, 2747, 727, -243, 85, -577, -1077, 534]

theorem fractionalNearFrameSubtreeG1R0025_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0025Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0025Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0025Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0025_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0025LowerBoundTable : List ℤ :=
  [3292, 3678, 2653, 4228, 265, 4381, 4692, 3438, 4787, 6235, 7492, -2783,
  5235, 2165, 6013, 4514, 2528, 2064, 8082, 8701, 8230, 391, 3704, 1832,
  4732]

def fractionalNearFrameSubtreeG1R0025LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0025Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0025LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
