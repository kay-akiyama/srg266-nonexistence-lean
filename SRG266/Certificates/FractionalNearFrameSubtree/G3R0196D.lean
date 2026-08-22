import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0196`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0196Mask : ℕ := 6867816530228756

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0196Witness : Array ℤ :=
  #[-166, -42, 108, 0, -8, 79, -71, -45, -136, 146, -83, 128, 17, 39, -11,
  111, 73, -119, 5, -73, -181, 174, 351, 139, 188, 176, -169, -197, -10,
  -339, -189, -86, -358, -238, 133, 365, 174, 12, 76, 253, 110, 139, -119,
  12, 35, 90, -135, 152, 32, -95, 72, 37, -56, 68, -130, 28, 210, -145, 177,
  125, -19, -8, 102, 7, -73, -12, -89, -108, 283, 198, 203, -75, -58, -29,
  62, -131, -142, 156, -241, -102, 45, -194, 107, 11, -7, -89, 98, 113, 228,
  161, 46, -45, -209, -51, 132, -47, 29, -70, 40, 33, -22, 98, 98, 104, 141,
  -100, 164, 101, -14, 53, 12, -220, 8, -33, 127, -189, -167, 33, 204, 171,
  74, 169, -108, -127, -93, -42, -46, -47, 13, -72, 95, 54, -56, -20, -89,
  -126, 72, 47, 44, 177, 120, -160, 202, -116, -45, 34, 22, -201, 32, 151,
  28, -49, 0, -22, 33, 71, 45, 187, 75, 121, -94, 163, 128, -135, 205, 48,
  102, 69]

theorem fractionalNearFrameSubtreeG3R0196_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0196Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0196Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0196Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0196_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0196LowerBoundTable : List ℤ :=
  [-14, 132, 126, 168, 200, 314, 69, 2, 201, 557, 169, 9, 453, 384, -400,
  289, 62, 85, 63, 933, 9, 511, 154, 591, 524]

def fractionalNearFrameSubtreeG3R0196LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0196Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0196LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
