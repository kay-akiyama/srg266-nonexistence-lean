import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0482`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0482Mask : ℕ := 5810353783424274

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0482Witness : Array ℤ :=
  #[766, -73, 702, 30, -101, 207, -1619, -1781, -1853, -1120, -1793, 950,
  1910, 1108, 1173, 1379, 1438, 516, 757, 1515, -288, 845, 883, 178, -952,
  518, -819, -1081, -2294, -718, -273, -346, -1406, 634, 1226, -401, -316,
  167, 997, 848, 724, 975, -934, 173, 11, -205, 379, -27, 312, 329, 36, 646,
  511, -33, 109, 273, 73, -953, -1174, 121, 1173, 1615, -300, 0, -526, 782,
  917, -345, -224, 239, 346, -752, -39, -833, -200, 32, 628, 1002, 682, 429,
  -83, 519, -208, 129, -659, 271, 495, 684, -205, 439, -353, 162, 1067, 321,
  34, 2027, 221, 110, -274, -99, 682, 1808, 1397, -450, -658, -55, -581,
  -183, -84, -943, -785, -372, 203, 401, -324, -681, -29, -525, -24, -376,
  -647, -284, 328, -15, -153, 175, 22, -652, 863, -522, 590, -258, -171,
  -494, 170, 140, -584, 15, -105, 528, 394, 250, 169, 117, -38, -206, 369,
  -1198, 536, -355, 403, 490, 181, -410, 108, 1276, -7, -176, 487, 670, 325,
  454, 925, -159, 232, 557, 525, -218]

theorem fractionalNearFrameSubtreeG2R0482_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0482Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0482Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0482Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0482_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0482LowerBoundTable : List ℤ :=
  [406, 894, 1947, 32, 1873, 3536, -870, 33, 1888, 161, -2663, 95, -412,
  2436, -678, 460, 2058, 1247, 2187, 2475, 670, 2909, 5618, -589, 2822]

def fractionalNearFrameSubtreeG2R0482LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0482Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0482LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
