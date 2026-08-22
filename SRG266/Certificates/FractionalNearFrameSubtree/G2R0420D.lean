import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0420`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0420Mask : ℕ := 5776741332882058

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0420Witness : Array ℤ :=
  #[-376, -375, -115, 491, -168, -29, -781, 381, 629, 426, -135, -132, -632,
  -150, -641, 662, 260, 222, 246, 551, 349, -219, 216, -1269, 200, 178, -2,
  281, 229, 99, -5, -711, -242, 640, 160, 109, 200, 402, 856, 255, -268,
  312, 414, -532, -201, -564, 141, -930, 423, -151, 774, 761, 889, 682,
  -115, 145, 364, 883, -90, -819, 285, -10, -128, -16, -523, -511, -983,
  1134, 305, 196, 485, 689, 317, -94, -673, 194, 339, 870, 549, 688, 65,
  -453, -780, 259, -347, 271, 1223, -92, -4, 700, 114, 298, 73, 668, 143,
  26, -825, 747, 296, -182, -277, 306, 826, -323, 271, -1307, -1009, 341,
  -21, -100, 561, -205, 976, 872, -633, 1005, 365, 377, -102, 543, 351,
  -1311, -1048, 411, 792, 970, -42, 985, 1287, -98, 464, -807, -929, -570,
  1043, -359, 626, -762, 623, -551, -483, 194, -656, 354, 991, 96, -667,
  -358, 66, 671, 537, 245, -100, -314, 70, 283, 38, -180, 163, 118, -275, 0,
  -142, -507, -87, 279, -505, -984]

theorem fractionalNearFrameSubtreeG2R0420_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0420Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0420Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0420Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0420_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0420LowerBoundTable : List ℤ :=
  [204, 303, -516, 1035, 1846, -308, -162, 1761, 876, 315, -405, 2974, 461,
  3756, -22, 98, 1438, 2854, 2179, 3472, -23, 3505, 3409, -2151, 1205]

def fractionalNearFrameSubtreeG2R0420LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0420Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0420LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
