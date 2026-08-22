import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0066`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0066Mask : ℕ := 1030915802960530

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0066Witness : Array ℤ :=
  #[540, 798, 69, -309, -304, 433, -617, -550, -818, -911, -489, -18, 169,
  0, -915, 1186, -438, 663, -255, -501, -993, 573, -279, 802, -110, -142,
  -121, 779, 568, 110, 444, -187, -38, 727, -838, 71, 3, -142, -768, -593,
  487, 495, -317, -316, -521, -825, 1162, 201, 400, 22, 938, 379, -858, 440,
  260, 698, 132, -61, -83, 854, -475, -793, 222, 898, -539, -613, 619, 42,
  61, -294, -842, 693, -239, -163, 298, -28, -576, -477, -541, -703, 215,
  401, 1293, 218, -24, 622, -57, 282, 586, 725, -372, 358, 148, 536, 737,
  55, 18, -490, 398, -656, 370, 107, 4, -262, -469, -349, -258, 213, 400,
  867, -961, -753, -821, 351, 65, -116, -111, -511, 132, 0, 0, 260, -743,
  -504, -345, 800, -585, -588, 619, -424, 715, -409, -663, 640, -155, -160,
  713, -242, 339, -318, -20, -185, 150, 1492, -7, -385, 898, 49, -243, 101,
  -297, 219, 178, 37, -112, -316, -195, -2, 0, 294, 598, 1260, -1020, -700,
  274, 774, -816, 36]

theorem fractionalNearFrameSubtreeG3R0066_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0066Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0066Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0066Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0066_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0066LowerBoundTable : List ℤ :=
  [-837, 32, 688, -741, -524, 1527, -125, -936, 838, 869, -363, -1290, -578,
  2461, 2494, 1259, -283, 2185, 1836, -3995, 518, 445, -2057, 2663, 1246]

def fractionalNearFrameSubtreeG3R0066LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0066Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0066LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
