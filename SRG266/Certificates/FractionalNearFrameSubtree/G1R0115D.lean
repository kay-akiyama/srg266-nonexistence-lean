import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0115`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0115Mask : ℕ := 969046110627084

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0115Witness : Array ℤ :=
  #[852, 318, 767, 800, -1282, 686, -372, 959, -1037, -818, 715, 746, 495,
  939, -321, -93, 367, -335, -502, 240, 164, 451, 120, 278, 174, -47, 648,
  365, 316, 435, 286, -493, -143, 140, -186, -258, -50, 244, 658, -434,
  -511, 167, -49, -86, -44, -273, 1041, -13, 222, 144, -492, -228, 844,
  -768, 457, 196, 348, 733, 328, -678, 599, -276, -270, 164, 279, 72, 398,
  336, -22, 22, -542, -708, 531, 172, -171, -863, 816, 237, 954, 479, 451,
  650, -517, -425, 466, -260, 774, 37, 496, 288, -325, 647, -413, 195, 188,
  -372, 27, 745, 1298, 334, 478, 198, 326, 976, 363, -186, -881, -306, -255,
  304, 620, -252, 314, 190, 110, 257, 154, -342, 365, 43, 1137, -63, -965,
  -328, -351, -172, 275, 326, -303, 162, 252, 271, 165, -140, 72, 91, 63,
  733, 587, -431, -1197, 598, -25, 201, 409, 620, -1, -346, -449, 182, 398,
  455, 248, 315, -30, -287, 291, 189, -111, 581, 186, -91, -60, -365, -440,
  -448, 120, 169]

theorem fractionalNearFrameSubtreeG1R0115_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0115Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0115Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0115Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0115_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0115LowerBoundTable : List ℤ :=
  [986, 1026, 616, 1666, 248, 1314, 1809, 2384, 811, 626, 102, 1040, 1402,
  99, 2289, 1334, 99, 4175, 3361, 3878, 2710, 1010, 1062, 99, 2465]

def fractionalNearFrameSubtreeG1R0115LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0115Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0115LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
