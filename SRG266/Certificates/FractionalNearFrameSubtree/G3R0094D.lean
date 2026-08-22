import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0094`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0094Mask : ℕ := 2512483545355348

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0094Witness : Array ℤ :=
  #[509, -623, 780, 0, -249, 408, 248, 545, 610, 201, -567, -271, 381, -836,
  154, -236, -597, -361, -277, -43, -251, 108, -145, 809, -77, 344, 15,
  -152, 56, -436, -299, -814, -170, -245, 392, -60, -2, 469, 261, 0, 245,
  -355, -179, -384, 218, -518, -775, 144, 99, -10, -163, 491, 180, -344,
  279, 921, -510, -108, -44, 352, -245, -589, 171, -260, -919, 142, -153,
  84, 294, 297, 693, -29, -371, -313, -44, -518, -522, 245, 751, 127, -155,
  532, 319, -3, 327, 2, -405, 100, -102, -238, 75, -338, 42, 79, 40, 181,
  706, -212, -211, 0, -310, 457, 268, -42, -160, -82, -103, 352, -116, -5,
  107, -142, -364, 195, -222, -187, 520, -275, -197, 106, 477, -52, 55,
  -620, -150, -33, -200, -185, 261, -221, 343, -109, -935, -203, -93, 284,
  -23, 218, 365, 0, 517, 286, 659, 634, 8, 234, -341, -1233, -732, 238, 385,
  142, -210, 718, 215, 17, 291, 303, -16, 968, 132, 192, 965, -344, -414,
  -833, 198, 156]

theorem fractionalNearFrameSubtreeG3R0094_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0094Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0094Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0094Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0094_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0094LowerBoundTable : List ℤ :=
  [-333, 526, -27, 379, 105, -582, 21, -323, -243, 101, 1096, -1771, 655,
  893, 101, 924, -1972, 2047, -412, 2161, 468, 883, -289, -390, 1931]

def fractionalNearFrameSubtreeG3R0094LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0094Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0094LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
