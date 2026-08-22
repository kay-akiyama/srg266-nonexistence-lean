import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0055`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0055Mask : ℕ := 936564347049098

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0055Witness : Array ℤ :=
  #[-458, 221, 135, 137, 113, 316, 258, 144, 219, -93, 236, -256, -167,
  -142, -302, 0, -454, 22, -233, -179, -32, -65, 37, -15, 88, 22, 235, -2,
  314, 509, -133, -12, 58, -236, -249, -98, -12, 48, 291, 306, 324, 560,
  116, -59, -59, 97, 198, -102, -27, -57, -143, -85, -103, -445, 233, 64,
  188, 319, 61, 18, -163, 197, 0, -111, -391, -160, -329, 47, -125, 30, 147,
  226, 407, 218, 125, 90, -56, 104, 170, 69, -131, 211, -38, -180, 27, -182,
  206, -153, 100, -99, 76, 255, 81, -155, 196, -158, 132, -176, 130, 44,
  109, -69, -220, -98, -285, -40, 113, -65, 16, -369, -221, 277, 141, 79,
  68, 165, 63, -31, 77, -154, 342, 170, -17, 53, 149, -26, 122, -146, -46,
  9, 40, 292, 499, -60, 0, 48, 177, 492, 308, 58, 159, 78, 86, 102, 350,
  282, 4, 39, 21, -63, -126, 191, 264, -82, -225, 135, -133, -319, 308, 409,
  343, -128, 428, 350, -290, -153, -281, -440]

theorem fractionalNearFrameSubtreeG2R0055_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0055Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0055Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0055Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0055_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0055LowerBoundTable : List ℤ :=
  [242, 872, 2, 835, -101, 352, 331, -4, 293, 634, 1349, 283, 910, 353,
  1367, -267, 912, 390, 368, 96, 1819, 53, -599, 824, 291]

def fractionalNearFrameSubtreeG2R0055LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0055Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0055LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
