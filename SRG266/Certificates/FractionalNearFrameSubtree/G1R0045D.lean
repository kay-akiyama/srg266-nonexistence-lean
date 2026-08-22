import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0045`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0045Mask : ℕ := 538515384971668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0045Witness : Array ℤ :=
  #[-126, -334, -386, -661, -461, -26, 227, -242, 66, 542, 468, 530, 271,
  -194, -237, -179, 0, -721, -944, 901, 901, 443, 65, 448, -188, -292, -163,
  147, -270, -372, -454, -371, 0, 62, 525, 180, -323, -56, 629, 380, 25,
  -77, -1056, -735, -329, -113, -154, 594, 233, 256, 237, -1061, -409, -46,
  84, -329, 27, 550, 246, -132, 264, -94, -376, 107, 0, -578, 120, 798,
  -1031, -1278, 1621, 289, 305, 9, 613, 268, -22, 473, 645, -658, -351, 709,
  15, 313, -154, 617, -204, 633, -103, -417, 150, 502, 490, 135, 902, -525,
  311, 304, 498, -513, 81, -321, -219, -285, 338, 33, 130, -376, -123,
  -1216, 0, -745, 0, -767, -264, 12, 19, 939, 1377, -274, -127, -224, 620,
  -130, 22, -531, -234, -154, 132, 970, 220, -228, -199, -55, 796, 73, 53,
  583, 397, 770, -190, 659, -320, 238, 516, -480, 244, 624, 81, 261, -850,
  -424, -215, -121, -1028, -342, 777, -676, 118, -189, -336, -234, 33, -744,
  -404, 518, -145, -85]

theorem fractionalNearFrameSubtreeG1R0045_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0045Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0045Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0045Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0045_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0045LowerBoundTable : List ℤ :=
  [-693, 16, -900, 505, -242, 30, 6, 32, 1684, 689, 930, -1732, -610, -851,
  -1507, -1119, 271, 1176, -881, 470, 1298, 99, 800, 933, 3556]

def fractionalNearFrameSubtreeG1R0045LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0045Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0045LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
