import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0204`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0204Mask : ℕ := 6880310195860136

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0204Witness : Array ℤ :=
  #[-233, -71, -21, 317, 55, 215, 36, 78, -96, -224, -28, 6, 9, 77, 107,
  285, 159, -235, 83, 105, 430, 255, -157, 580, -542, 152, -94, -619, 165,
  -214, 406, 203, 539, -506, -521, 746, 340, 658, -381, -727, 198, 509, 444,
  -270, -109, 905, -286, -98, 217, -173, -212, 272, -437, 287, 222, -97,
  -93, -257, 18, 1089, 655, -585, 599, -111, 246, 512, -63, 330, 525, -282,
  24, 247, 107, -435, 452, 95, 522, 63, -301, 148, 16, 104, 225, -408, -138,
  -71, 247, 214, 280, -35, -315, 475, 188, -249, -311, -580, -256, -178,
  -14, -522, -376, -44, 235, 242, -199, 0, -71, -336, 483, -399, -436, -580,
  -141, 237, 240, 120, 99, 79, 21, -4, -656, -408, -162, -141, 273, 11,
  -170, 157, 79, -428, -69, -580, -184, 211, 113, -66, 302, 64, 240, -183,
  96, -517, 0, 155, -457, 591, -529, -348, -134, -293, 48, 10, -294, 234,
  287, -203, 264, 160, 37, 344, 306, 93, 100, 168, 488, 292, 531, 280]

theorem fractionalNearFrameSubtreeG3R0204_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0204Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0204Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0204Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0204_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0204LowerBoundTable : List ℤ :=
  [-126, 100, 1252, 76, 32, 64, 176, -63, 156, -11, 1124, 99, 685, 2012,
  -440, 1797, 2211, 145, -330, -548, 736, 149, 1509, 100, 829]

def fractionalNearFrameSubtreeG3R0204LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0204Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0204LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
