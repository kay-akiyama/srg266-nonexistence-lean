import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0388`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0388Mask : ℕ := 5739232000169112

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0388Witness : Array ℤ :=
  #[789, -358, -754, 757, -179, 65, 580, 15, 875, 194, 511, 443, -1114,
  -225, 338, -229, -458, -53, 76, 236, -22, -229, 1101, -604, 143, 210, 42,
  174, 485, 199, 54, 33, 1341, 41, 924, -91, -362, -580, -46, -441, -155,
  -799, -282, 901, 1163, -266, 605, 823, -290, 101, -2, -4, 687, -192, 789,
  -1243, 762, -274, -540, 92, -235, 62, -242, 817, 131, 1211, 420, 440,
  -1379, -297, 144, 610, -433, -250, 366, 711, 441, 745, 122, -680, -324,
  -102, 423, -335, 816, 252, 487, 390, -277, -109, -98, 126, 495, -1480,
  308, 93, 645, -687, -406, -457, 151, 407, 126, 214, -846, -988, -89, -68,
  -24, 342, 686, 4, 50, 1326, 0, 748, 759, 1240, 1240, -441, -850, -1283,
  -775, -737, 1143, 703, 248, 224, 767, 0, -143, -379, 316, -189, 503, -353,
  406, 211, -1316, 1451, 1337, -1305, 154, -1146, 1096, 779, 752, 902, 529,
  421, 86, -274, 133, -294, 843, -922, -2, 612, -436, -339, 136, 231, 304,
  256, 253, -48, 446, 122]

theorem fractionalNearFrameSubtreeG2R0388_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0388Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0388Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0388Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0388_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0388LowerBoundTable : List ℤ :=
  [534, 1491, -494, 1128, 2782, 120, 889, 2492, 823, 3184, 266, 1862, -238,
  1513, 1895, 252, 8, 4091, 171, 100, 3132, 4369, 2016, 2594, 946]

def fractionalNearFrameSubtreeG2R0388LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0388Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0388LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
