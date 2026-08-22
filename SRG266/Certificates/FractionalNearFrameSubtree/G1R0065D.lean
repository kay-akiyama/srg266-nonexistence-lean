import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0065`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0065Mask : ℕ := 827751356875154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0065Witness : Array ℤ :=
  #[-616, 667, -370, -712, 598, -271, 802, 1109, -12, -186, -447, 22, -293,
  462, 249, -534, 0, 384, -715, -277, 1110, -641, 110, -563, 1004, -405, 0,
  -575, 287, 783, 185, 303, -13, 13, -722, 22, 13, 144, 505, 136, 25, -321,
  842, 506, 180, -40, 384, 470, -237, -150, -183, 599, -199, 9, -674, -539,
  63, 126, 383, 581, -245, 4, -296, -319, -300, -70, -501, -21, -379, -391,
  -17, 265, 117, 367, -173, -177, -8, 157, 231, 105, 90, 249, 543, -176,
  -253, 76, -9, 64, -314, -343, 68, -128, 388, 127, 309, -1245, -488, -157,
  326, 213, 486, 458, 533, 751, 289, 357, -359, -103, 161, 155, -326, 239,
  90, 84, -354, -259, 110, 230, 169, 177, 105, -635, -102, -283, -186, 217,
  -31, 34, 32, -384, -463, 273, 0, -543, -225, -445, -57, -13, -115, 95,
  -1138, 93, 149, 404, 167, -38, -22, -147, 214, 161, 144, -329, 336, -619,
  509, 388, 833, 440, 273, 114, -119, 345, 799, 435, -1, -691, 247, -577]

theorem fractionalNearFrameSubtreeG1R0065_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0065Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0065Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0065Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0065_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0065LowerBoundTable : List ℤ :=
  [-17, 32, -142, 815, -196, 681, 450, 31, 1530, -1507, 277, 1108, 354,
  -1202, -283, 417, 264, 1477, -611, -551, -493, -936, 2009, 588, 2898]

def fractionalNearFrameSubtreeG1R0065LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0065Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0065LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
