import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0117`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0117Mask : ℕ := 5389445714512488

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0117Witness : Array ℤ :=
  #[628, -579, 109, -235, -163, 667, -277, -345, -234, -26, 771, 904, -275,
  32, 220, -588, 205, 430, 97, 422, -139, -202, 229, 332, -931, -279, -474,
  -148, 706, -246, 145, -33, -381, 184, 123, -355, -682, 482, -662, -481,
  -702, -32, 9, -521, -105, -944, 356, 285, 483, 721, 407, -252, 722, 604,
  -145, -7, 0, 7, -3, -77, 151, -644, -587, 350, -622, -225, 673, 406, -811,
  -33, 818, 45, -244, -305, 90, 261, -477, 220, 251, 145, -234, 269, 209,
  105, -37, -199, -88, 80, -317, 16, 213, 122, -9, -197, -85, -358, 446,
  -213, -631, 177, -38, 102, -1, 1206, 89, 598, 699, -551, -837, -1370,
  -518, 240, -287, 380, 366, 539, 633, 678, 314, 125, 144, -330, 354, 140,
  -99, -567, -163, 593, 0, 264, -235, 1033, 1, 317, 137, -179, -47, 550,
  469, 475, -398, -437, 192, 193, 545, 188, -223, 381, -671, -151, 60, -437,
  307, -490, -573, -519, 246, 72, 638, -242, -1317, -32, 253, 903, 806, 954,
  685, -206]

theorem fractionalNearFrameSubtreeG3R0117_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0117Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0117Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0117Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0117_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0117LowerBoundTable : List ℤ :=
  [-366, 1458, 32, 32, 917, 32, -1096, 32, 890, 135, 1786, -341, 1189, 1227,
  2098, -1168, 947, 1327, 713, -547, 39, 72, -36, -1006, 3655]

def fractionalNearFrameSubtreeG3R0117LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0117Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0117LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
