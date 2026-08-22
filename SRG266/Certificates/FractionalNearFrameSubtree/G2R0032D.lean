import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0032Mask : ℕ := 866255881605635

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0032Witness : Array ℤ :=
  #[-127, 15, -110, -181, -358, -157, 108, -21, 28, 45, -50, -150, 266, 345,
  82, 295, 269, 93, 207, 92, 71, -20, 108, 254, 0, -67, -105, -278, -188,
  -45, 10, 4, 17, 303, 207, 285, -68, -76, -232, -143, 31, -285, 171, -158,
  138, 12, 6, -44, -79, 24, -55, 64, 67, 32, 33, 97, 93, 40, 62, 146, -61,
  -5, 31, 17, -41, 28, 36, -236, -98, 59, 35, -21, 75, -198, 84, 97, -43,
  -42, -38, -2, 76, 95, 159, 206, 46, 46, -5, 95, 65, -12, 167, 13, 91, 134,
  88, -26, -111, -119, -59, -63, 77, -140, -72, -4, -126, -193, 97, 120,
  149, 19, -31, 28, 229, 23, -1, 63, -6, -19, -31, 28, 93, 10, 13, 144, 65,
  50, 19, -13, -54, -37, 387, -83, 13, -48, 51, 139, -197, -18, -182, 4,
  162, -1, -63, 62, 51, 46, -150, 259, -18, 41, 44, 206, 131, 61, 146, 248,
  12, -88, -54, 218, 0, -320, 106, -93, -49, -135, -214, 168]

theorem fractionalNearFrameSubtreeG2R0032_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0032Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0032Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0032Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0032_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0032LowerBoundTable : List ℤ :=
  [71, 277, 2, 269, 2, 102, 2, 381, 404, 496, 205, 653, -50, 50, -109, 626,
  453, 253, 798, 519, 9, -113, 571, 96, 309]

def fractionalNearFrameSubtreeG2R0032LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0032Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0032LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
