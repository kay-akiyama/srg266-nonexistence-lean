import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0376`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0376Mask : ℕ := 5737087014741130

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0376Witness : Array ℤ :=
  #[185, 21, 427, 727, -384, 359, 750, 91, -870, 838, -532, -324, -1136, 81,
  2, 442, 639, 131, -101, 219, 785, 159, -443, -762, -426, -681, 757, -48,
  -23, 580, -204, 1094, 424, 589, -731, 158, 221, -449, -335, -153, 484,
  -377, 0, 285, 665, 367, -529, -563, -80, 172, 404, -242, 187, -119, 858,
  88, 666, 156, 607, -284, -166, -200, 471, 65, 46, 680, -290, 399, 1228,
  629, 315, -381, -634, -666, 633, -241, 1363, 719, 862, 1022, -777, -469,
  -614, -698, -419, -581, -932, -295, 1118, -375, 11, -7, 837, 788, 86,
  -644, -521, -923, 13, -275, 115, 200, 249, -151, -17, -31, 354, 248, 216,
  -780, -150, 1006, 1091, -143, -94, -852, -1408, -222, -92, -884, -926,
  -592, -882, -88, 1379, -437, -277, -707, -174, 206, -213, 334, 518, 175,
  15, 155, -369, 188, 175, 540, 321, 187, 543, 353, 173, -857, -267, 676,
  135, -555, -10, 259, 200, 111, 216, -9, -427, 957, 169, 292, -39, -397,
  -183, -168, -269, -134, 153, 203]

theorem fractionalNearFrameSubtreeG2R0376_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0376Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0376Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0376Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0376_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0376LowerBoundTable : List ℤ :=
  [-225, -498, 85, 1213, 572, 32, 30, 760, 908, -714, 1180, -1927, 2453,
  830, -282, 1153, 3078, 1260, -466, 2003, -1968, 584, 3463, -895, 99]

def fractionalNearFrameSubtreeG2R0376LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0376Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0376LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
