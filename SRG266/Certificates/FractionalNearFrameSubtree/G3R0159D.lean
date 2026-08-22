import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0159`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0159Mask : ℕ := 6850697605028520

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0159Witness : Array ℤ :=
  #[90, -63, 1056, 159, 190, -232, -225, 0, -325, -139, 120, 433, 288, -269,
  401, 787, 240, -127, 88, -182, 1498, 549, 469, 216, -247, -743, -223,
  -729, -178, -356, -602, 644, 1198, 483, 11, 629, -684, -531, 6, -97, 104,
  112, -177, -69, 551, 483, -347, -1276, -560, -1233, 1075, 240, 763, -215,
  573, -264, 734, 365, -709, -530, -747, -1249, 1097, -378, -179, 269, -30,
  -284, 256, -85, 184, 1053, -893, 113, 101, 622, 865, -510, -26, -51, -53,
  -261, 402, -738, 1185, -1276, 482, 233, -808, -289, -51, 0, 96, 177, 857,
  -727, 917, -53, 514, -324, -59, 554, 407, -266, 922, -137, 283, 966, -841,
  69, -233, 372, -324, 1362, 111, 126, 209, -138, 622, -1872, 658, 164,
  -393, 326, -72, 195, -717, 994, -627, 826, -638, 411, 270, -457, 79, 9,
  286, -452, 282, 207, -244, 670, 37, -364, -171, -1471, 697, 749, -44, 70,
  -249, 23, 816, -222, -791, -148, 259, -908, -119, 1152, 58, -250, 1040,
  952, 1018, -330, -640, 628]

theorem fractionalNearFrameSubtreeG3R0159_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0159Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0159Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0159Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0159_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0159LowerBoundTable : List ℤ :=
  [98, 912, 361, 32, -1004, 671, 653, 1666, 262, 2526, 2056, 2633, -1927,
  101, -2795, 773, 385, 2132, -375, 737, 3613, 100, 3767, 1875, 4010]

def fractionalNearFrameSubtreeG3R0159LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0159Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0159LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
