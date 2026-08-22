import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0173`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0173Mask : ℕ := 1380484507353700

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0173Witness : Array ℤ :=
  #[97, 74, 54, 158, 15, 60, -244, -45, -143, -194, -116, 175, 6, -57, 59,
  55, 73, -1, -73, -87, 25, 65, -225, -55, -58, -201, 128, 11, 113, 14, 13,
  -16, 138, 56, 251, -21, -53, 79, 29, -52, -57, -38, -160, -90, 17, -18,
  23, -12, 169, 39, 200, 74, -25, -85, -26, -93, -20, -68, 132, 10, 44, 210,
  -222, -86, 56, -85, 92, 137, 151, 120, -123, 34, -17, 46, 111, 75, 85, 64,
  -71, 107, 144, 259, 4, 72, -37, 82, 187, 25, -62, -79, -40, 41, 12, -38,
  67, 0, 49, -174, -24, 60, 125, -185, 28, 89, -50, 164, -59, 8, -88, -44,
  -83, -144, 11, -72, -9, -282, -221, -258, 151, 106, 1, 74, 123, 221, 77,
  -61, -123, 67, -10, 0, 68, 1, 132, 139, 144, -28, -25, 183, 93, 18, 4,
  201, -156, 4, 198, 174, 60, -16, 141, 41, 137, 186, 48, -70, -220, -66, 6,
  -90, -167, 283, -27, -80, 25, 199, -69, -19, -7, -68]

theorem fractionalNearFrameSubtreeG2R0173_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0173Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0173Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0173Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0173_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0173LowerBoundTable : List ℤ :=
  [-16, 308, -45, 84, 1, 282, 78, 99, 343, 816, 395, 11, 142, 147, 11, 11,
  19, 10, 498, -196, 419, 288, 465, 286, 356]

def fractionalNearFrameSubtreeG2R0173LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0173Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0173LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
