import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0303`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0303Mask : ℕ := 5387218973142168

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0303Witness : Array ℤ :=
  #[338, -429, 821, -933, -225, 463, 167, 669, 9, 283, -214, 520, -109,
  -397, 108, -568, 618, 688, -209, 238, -107, 98, 126, 17, -82, -17, -408,
  282, 414, -197, 164, 711, -428, -277, -632, 1226, -163, -233, 116, -110,
  394, -225, -808, 589, -188, 743, -278, -202, 76, -107, -321, 350, 477,
  666, -308, 512, 587, -672, -455, 0, 275, -148, -925, 58, 0, -628, -1398,
  -573, 1117, -611, 205, 1506, 418, 122, 905, 1346, 817, 485, 76, 70, 145,
  517, 465, 704, 10, 112, 213, 259, -529, 288, 52, -91, 657, -234, -646,
  428, 401, 39, -715, 617, 0, -642, 236, -160, -582, -320, 269, -1009, 122,
  465, 260, 749, 22, 0, -1010, -304, 221, -590, -135, -640, -313, -200, 686,
  472, -1360, 642, 548, 433, 466, 738, 435, -211, -31, -82, 552, -397, 799,
  774, 476, -23, -201, -519, -588, 445, 766, -171, 118, -889, -286, 467,
  -555, 809, -536, 833, -702, -738, 112, 72, -464, -311, 1006, 24, 538,
  -369, 486, 727, 0, 97]

theorem fractionalNearFrameSubtreeG2R0303_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0303Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0303Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0303Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0303_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0303LowerBoundTable : List ℤ :=
  [109, 689, 1416, 1491, -669, -533, 669, 2047, 1352, 102, 1253, 1766, -775,
  -307, 1996, 1627, 4609, 1688, -1685, 2368, 98, -1573, 752, 1212, 1209]

def fractionalNearFrameSubtreeG2R0303LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0303Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0303LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
