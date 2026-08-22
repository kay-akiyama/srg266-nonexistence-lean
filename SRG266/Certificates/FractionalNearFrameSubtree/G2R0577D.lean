import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0577`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0577Mask : ℕ := 6850422057190488

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0577Witness : Array ℤ :=
  #[-592, 133, 130, -139, 580, 315, 241, 490, -341, -86, -53, -430, -492,
  188, -896, -175, -214, -65, 903, 449, 665, 111, -49, -472, -226, -285,
  -680, 252, -795, -850, -663, -95, 265, 193, 144, 247, 930, -130, 414,
  1466, 181, 873, -167, -100, 467, 615, 255, -21, -26, -130, 242, 657, -143,
  -485, 258, -228, 791, 395, -375, 475, 139, 672, -393, 73, -230, 94, 7,
  127, 147, 933, -234, 17, 573, -185, 0, -130, -103, 870, 148, 598, 280,
  119, 674, 437, 140, 288, 1246, 357, -381, -679, -96, -236, -314, -420,
  140, 437, 108, -275, -50, 138, 20, -271, -176, 25, -113, -1355, -804,
  -367, 368, 601, 152, -490, 274, 590, 407, -858, -286, -965, 648, -342,
  273, -695, -384, 251, -585, -3, 102, 573, -597, -373, -359, 194, 563, 561,
  552, -181, -35, -457, 421, 280, 543, 383, 261, 1003, 138, 524, 62, -145,
  641, -96, -25, 1704, 698, 434, 1857, -113, 642, 806, 690, -107, 825, 106,
  -397, -364, 0, 321, 845, 208]

theorem fractionalNearFrameSubtreeG2R0577_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0577Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0577Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0577Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0577_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0577LowerBoundTable : List ℤ :=
  [904, 2109, 2492, 1476, 619, 1159, 603, 1409, 0, 2553, 10, 1249, 1649,
  909, 868, 2310, -428, 4346, 861, 2650, 822, 1367, 298, 10, 1104]

def fractionalNearFrameSubtreeG2R0577LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0577Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0577LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
